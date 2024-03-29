//===-- Frequent Path Loop Invariant Code Motion Pass
//------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// EECS583 F22 - This pass can be used as a template for your Frequent Path LICM
//               homework assignment. The pass gets registered as "fplicm".
//
// This pass performs loop invariant code motion, attempting to remove as much
// code from the body of a loop as possible.  It does this by either hoisting
// code into the preheader block, or by sinking code to the exit blocks if it is
// safe.
//
////===----------------------------------------------------------------------===//
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/Trace.h"
#include "llvm/Analysis/PostDominators.h"

/* *******Implementation Starts Here******* */
// include necessary header files
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include <deque>
#include <cassert>
/* *******Implementation Ends Here******* */

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "fplicm"

// Recursively finds all subloops in a loop
std::vector<Loop*> GetAllSubLoops(Loop* L) {
  std::vector<Loop*> allLoops;
  for (Loop *SL : L->getSubLoops()) {
    std::vector<Loop*> subLoops = GetAllSubLoops(SL);
    allLoops.insert(allLoops.end(), subLoops.begin(), subLoops.end());
  }
  allLoops.push_back(L);
  return allLoops;
}

// Find all loops given a loop info
std::vector<Loop*> FindAllLoops(LoopInfo &LI) {
  std::vector<Loop*> loops;
  for (Loop* L : LI) {
    std::vector<Loop*> containedLoops = GetAllSubLoops(L);
    loops.insert(loops.end(), containedLoops.begin(), containedLoops.end());
  }
  return loops;
}

bool CompareLoopDepth(Loop* L1, Loop* L2) {
    return L1->getLoopDepth() > L2->getLoopDepth();
}

    bool containHazard(BasicBlock* bb) {
    //   errs()<<"Processing containHazard for block "<<bb->getName()<<'\n';
      for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
          string op = i->getOpcodeName();
          if (op=="call") // subroutine call
            return true;
          if (i->isAtomic()) // sync instr
            return true;
          if (op=="store") { // ambiguous store
            Value *oper = i->getOperand(1); // get the store destination
            if (Instruction *stdestInstr = dyn_cast<Instruction>(oper)) {
                string stdestOp = stdestInstr->getOpcodeName();
                // errs()<<"store destination instr: "<< stdestOp<<'\n';
                if (stdestOp=="alloca") {
                    // errs()<<"not hazard"<<'\n';
                    continue; // known at compile time
                }
                if (GetElementPtrInst *GEPInstr = dyn_cast<GetElementPtrInst>(stdestInstr)) {
                    if (GEPInstr->hasAllConstantIndices()) {
                        if (Instruction *ptrInstr = dyn_cast<Instruction>(GEPInstr->getPointerOperand())) {
                            string ptrOp = ptrInstr->getOpcodeName();
                            if (ptrOp=="alloca") {
                                // errs()<<"not hazard"<<'\n';
                                continue; // known at compile time
                            }
                        }
                    }
                }
                return true; // otherwise unknown at compile time
              }
          }
          if (op=="ret") // subroutine return
              return true;
          if (op=="indirectbr") // indirect jump
              return true;
      }
    //   errs()<<"Block "<<bb->getName()<<" has no hazard!"<<'\n';
      return false;
    }

namespace BaseTrace {
  struct BaseTracePass : public FunctionPass {
    static char ID;
    BaseTracePass() : FunctionPass(ID) {};
    BaseTracePass(char id): FunctionPass(id) {};

    Trace GrowTrace(BasicBlock* seedBB, DominatorTree &DT, PostDominatorTree &PDT, Function &F, BranchProbabilityInfo &BPI) {
      std::vector<BasicBlock*> trace;
      BasicBlock *currBB = seedBB;
      while (1) {
        trace.push_back(currBB);
        visited.insert(currBB);
        BasicBlock *likelyBB = predict(currBB, F, PDT, BPI);
        if (!likelyBB || visited.find(likelyBB) != visited.end()) {break;}
        if (DT.dominates(&likelyBB->front(), &currBB->front())) {break;}
        currBB = likelyBB;
      }
      return Trace(trace);
    }

    bool runOnFunction(Function &F) override {
      LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      PostDominatorTree &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
      BranchProbabilityInfo &BPI = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
      BlockFrequencyInfo &BFI = getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

      prepare(F, LI, PDT);

      std::vector<Loop*> allLoops = FindAllLoops(LI);

      // sort the loops based on depth
      std::sort(allLoops.begin(), allLoops.end(), CompareLoopDepth);

      // create block list based on loop
      for (Loop* L : allLoops) {
        errs() << "\nLoop " << L->getLoopDepth() << '\n';
        for (BasicBlock* BB : L->getBlocksVector()) {
          if (visited.find(BB) == visited.end() && !inSubLoop(BB, L, &LI)) {
            traces.push_back(GrowTrace(BB, DT, PDT, F, BPI));
          }
          // errs() << BB->getName() << '\n';
        }
      }

      // errs() << "\nFunc\n";
      for (BasicBlock &BB : F) {
        if (visited.find(&BB) == visited.end()) {
          traces.push_back(GrowTrace(&BB, DT, PDT, F, BPI));
        }
        // errs() << BB.getName() << '\n';
      }

      // evaluation
        double total_in = 0;
        double total_out = 0;
        int total_hazard = 0;
        for (Trace trace : traces) {
            if (trace.size() <= 1) continue;
            BasicBlock *head = *(trace.begin());
            int totalHazard = 0;
            uint64_t init_in_count = BFI.getBlockProfileCount(head).getValue();
            uint64_t in_count = init_in_count;
            double out_count = in_count;
            for (Trace::iterator TI = trace.begin(); TI != trace.end(); ++TI) {
                BasicBlock *BB = *TI;
                //errs() << "Starting at " << BB->getName() << '\n';
                if (containHazard(BB)) {
                    totalHazard++;
                }
                for (BasicBlock *succ : successors(BB)) {
                    if (trace.contains(succ)) {
                        BranchProbability succ_bpi = BPI.getEdgeProbability(BB, succ);
                        double bp_double = succ_bpi.getNumerator() / double(succ_bpi.getDenominator());
                        //uint64_t succ_count = BFI.getBlockProfileCount(succ).getValue();
                        //errs() << "succ: " << succ_count << succ->getName() << '\n';
                        
                        out_count = in_count * bp_double;
                        
                        //errs() << "new in_count: " << in_count << '\n';
                        //errs() << "new out_count: " << out_count << '\n';
                        in_count = out_count;
                    }
                }
            }
            total_in += init_in_count;
            total_out += out_count;
            total_hazard += totalHazard;
            errs() << "\nTrace: size " << trace.size() << '\n';
            errs() << "Num of hazards: " << totalHazard << '\n';
            errs() << "in_count: " << init_in_count << '\n';
            errs() << "out_count: " << format("%.3f" ,out_count) << '\n';
            errs() << "fall thru: " << format("%.3f" ,out_count / init_in_count) << "\n\n";
        }
        //errs() << "total in count: " << init_in_count << '\n';
        errs() << "total hazard: " << total_hazard << '\n';
        errs() << "average fall thru: " << format("%.3f" , total_out / total_in) << "\n\n";



      //for (Trace trace : traces) {
      //  errs() << "\nTraces:\n";
      //  for (BasicBlock *traceBB : trace) {
      //    errs() << traceBB->getName() << '\n';
      //  }
      //}
      
      return false;
    }
    
    virtual void prepare(Function &F, LoopInfo &LI, PostDominatorTree &PDT) {

    }

    virtual BasicBlock* predict(BasicBlock *BB, Function &F, PostDominatorTree &PDT, BranchProbabilityInfo &BPI) {
      return nullptr;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<BranchProbabilityInfoWrapperPass>();
      AU.addRequired<BlockFrequencyInfoWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<PostDominatorTreeWrapperPass>();
    }
    protected:
    uint32_t thresProb = uint32_t((1u << 31) * 0.6);
    private:
    std::set<BasicBlock*> visited;
    std::vector<Trace> traces;
    /// Little predicate that returns true if the specified basic block is in
    /// a subloop of the current one, not the current one itself.
    bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
      assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
      return LI->getLoopFor(BB) != CurLoop;
    }
  };
}

char BaseTrace::BaseTracePass::ID = 0;
static RegisterPass<BaseTrace::BaseTracePass>
    B("base",
      "base trace formation", false, false);

namespace StaticTrace {
  struct StaticTracePass : public BaseTrace::BaseTracePass {
    static char ID;
    StaticTracePass() : BaseTracePass(ID) {};
    StaticTracePass(char id): BaseTracePass(id) {};

    virtual void prepare(Function &F, LoopInfo &LI, PostDominatorTree &PDT) override {
      for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
          for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
              if (BranchInst *Ibr = dyn_cast<BranchInst>(&(*i))) { // branch instr
                  if (Ibr->isConditional()) { // conditional branch
                      Value *cond = Ibr->getCondition();
                      Instruction *Icond = dyn_cast<Instruction>(cond);
                      Value *op0 = Icond->getOperand(0);
                      Value *op1 = Icond->getOperand(1);
                      pair<Value*, Value*> brOps = make_pair(op0, op1);
                      pair<int, bool> brPred;
                      auto res = brdirMap.find(brOps);
                      if (ICmpInst *ICC = dyn_cast<ICmpInst>(Icond)) {
                          if (op0->getType()->isPointerTy()) {
                          // the two operands must be the same type, enough to check one
                              if (ICC->getPredicate()==CmpInst::ICMP_EQ) { // beq
                                  brPred = make_pair(1, true); // label2 is likely
                                  brdirMap[brOps] = brPred;
                              }
                              if (ICC->getPredicate()==CmpInst::ICMP_NE) { // bne
                                  brPred = make_pair(1, false); // label1 is likely
                                  brdirMap[brOps] = brPred;
                              }
                          }
                          if (Constant *const0 = dyn_cast<Constant>(op0)) {
                              if (const0->isZeroValue()) {
                                  if (ICC->getPredicate()==CmpInst::ICMP_SGT | 
                                      ICC->getPredicate()==CmpInst::ICMP_UGT) { // greater than
                                      brPred = make_pair(3, true); // label2 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                                  if (ICC->getPredicate()==CmpInst::ICMP_SLE |
                                      ICC->getPredicate()==CmpInst::ICMP_ULE) { // less or equal
                                      brPred = make_pair(3, false); // label1 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                              }
                          }
                          if (Constant *const1 = dyn_cast<Constant>(op1)) {
                              if (const1->isZeroValue()) {
                                  if (ICC->getPredicate()==CmpInst::ICMP_SLT |
                                      ICC->getPredicate()==CmpInst::ICMP_ULT) { // less than
                                      brPred = make_pair(3, true); // label2 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                                  if (ICC->getPredicate()==CmpInst::ICMP_SGE |
                                      ICC->getPredicate()==CmpInst::ICMP_UGE) { // greater or equal
                                      brPred = make_pair(3, false); // label1 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                              }
                          }
                      }
                      if (FCmpInst *FCC = dyn_cast<FCmpInst>(Icond)) {
                          if (FCC->getPredicate()==CmpInst::FCMP_OEQ |
                              FCC->getPredicate()==CmpInst::FCMP_UEQ) { // beq
                              brPred = make_pair(3, true); // label2 is likely
                              res = brdirMap.find(brOps);
                              if (res != brdirMap.end()) {
                                  if ((res->second).first<3) {}
                                  else brdirMap[brOps] = brPred;
                              }
                              else brdirMap[brOps] = brPred;
                          }
                          if (FCC->getPredicate()==CmpInst::FCMP_ONE |
                              FCC->getPredicate()==CmpInst::FCMP_UNE) { // bne
                              brPred = make_pair(3, false); // label1 is likely
                              res = brdirMap.find(brOps);
                              if (res != brdirMap.end()) {
                                  if ((res->second).first<3) {}
                                  else brdirMap[brOps] = brPred;
                              }
                              else brdirMap[brOps] = brPred;
                          }
                          if (Constant *const0 = dyn_cast<Constant>(op0)) {
                              if (const0->isZeroValue()) {
                                  if (FCC->getPredicate()==CmpInst::FCMP_OGT |
                                      FCC->getPredicate()==CmpInst::FCMP_UGT) { // greater than
                                      brPred = make_pair(3, true); // label2 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                                  if (FCC->getPredicate()==CmpInst::FCMP_OLE |
                                      FCC->getPredicate()==CmpInst::FCMP_ULE) { // less or equal
                                      brPred = make_pair(3, false); // label1 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                              }
                          }
                          if (Constant *const1 = dyn_cast<Constant>(op1)) {
                              if (const1->isZeroValue()) {
                                  if (FCC->getPredicate()==CmpInst::FCMP_OLT |
                                      FCC->getPredicate()==CmpInst::FCMP_ULT) { // less than
                                      brPred = make_pair(3, true); // label2 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                                  if (FCC->getPredicate()==CmpInst::FCMP_OGE |
                                      FCC->getPredicate()==CmpInst::FCMP_UGE) { // greater or equal
                                      brPred = make_pair(3, false); // label1 is likely
                                      res = brdirMap.find(brOps);
                                      if (res != brdirMap.end()) {
                                          if ((res->second).first<3) {}
                                          else brdirMap[brOps] = brPred;
                                      }
                                      else brdirMap[brOps] = brPred;
                                  }
                              }
                          }
                      }
                      
                      bool inloop[2] = {0, 0}; // for branch direction heuristic
                      bool inloopPrehead[2] = {0, 0}; // for loop heuristic
                      for (unsigned bridx = 0; bridx < 2; bridx++) {
                          BasicBlock *Succ = Ibr->getSuccessor(bridx);
                          for (Loop* L : LI) {
                              BasicBlock *preHead = L->getLoopPreheader();
                              if (preHead==Succ) inloopPrehead[bridx] = 1;
                              vector<BasicBlock *> allBlocks = L->getBlocks();
                              if (find(allBlocks.begin(), allBlocks.end(), Succ) != allBlocks.end())
                                  inloop[bridx] = 1;
                          }
                      }
                      res = brdirMap.find(brOps);
                      if (inloopPrehead[0] & !inloopPrehead[1]) {
                          brPred = make_pair(2, false); // label1 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<2) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                      if (!inloopPrehead[0] & inloopPrehead[1]) {
                          brPred = make_pair(2, true); // label2 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<2) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                      res = brdirMap.find(brOps);
                      if (inloop[0] & !inloop[1]) {
                          brPred = make_pair(5, false); // label1 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<5) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                      if (!inloop[0] & inloop[1]) {
                          brPred = make_pair(5, true); // label2 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<5) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                      
                      bool leadtouse[2] = {0, 0}; // for guard heuristic
                      for (unsigned bridx = 0; bridx < 2; bridx++) {
                          for (Function::iterator bIt = F.begin(), END = F.end(); bIt != END; ++bIt) {
                              if (PDT.dominates(&bIt->front(), &Ibr->getSuccessor(bridx)->front())) {
                                  for (User *op0User : op0->users()) {
                                      if (Instruction *Iop0User = dyn_cast<Instruction>(op0User)) {
                                          BasicBlock *Iop0UserBlock = Iop0User->getParent();
                                          if (&(*bIt)==Iop0UserBlock) leadtouse[bridx] = 1;
                                      }
                                  }
                                  for (User *op1User : op1->users()) {
                                      if (Instruction *Iop1User = dyn_cast<Instruction>(op1User)) {
                                          BasicBlock *Iop1UserBlock = Iop1User->getParent();
                                          if (&(*bIt)==Iop1UserBlock) leadtouse[bridx] = 1;
                                      }
                                  }
                              }
                          }
                      }
                      res = brdirMap.find(brOps);
                      if (leadtouse[0] & !leadtouse[1]) {
                          brPred = make_pair(4, false); // label1 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<4) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                      if (!leadtouse[0] & leadtouse[1]) {
                          brPred = make_pair(4, true); // label2 is likely
                          if (res != brdirMap.end()) {
                              if ((res->second).first<4) {}
                              else brdirMap[brOps] = brPred;
                          }
                          else brdirMap[brOps] = brPred;
                      }
                  }
              }
          }
      }
    }

    virtual BasicBlock* predict(BasicBlock *BB, Function &F, PostDominatorTree &PDT, BranchProbabilityInfo &BPI) override {
      if (containHazard(BB)) return nullptr;
      Instruction *T = BB->getTerminator();
      if (BranchInst *brInst = dyn_cast<BranchInst>(T)) {
          if (brInst->isConditional()) { // conditional branch
              Instruction *Icond = dyn_cast<Instruction>(brInst->getCondition());
              pair<Value*, Value*> brOps = make_pair(Icond->getOperand(0), Icond->getOperand(1));
              bool hasHazard[2] = {0, 0};
              for (unsigned bridx = 0; bridx < 2; bridx++) {
                  BasicBlock *Succ = brInst->getSuccessor(bridx);
                  if (containHazard(Succ)) hasHazard[bridx] = 1;
                  /*for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                      if (PDT.dominates(&bb->front(), &Succ->front()))
                          if (containHazard(&(*bb))) hasHazard[bridx] = 1;
                  }*/
              }
              if (hasHazard[0] & !hasHazard[1]) return brInst->getSuccessor(1);
              if (!hasHazard[0] & hasHazard[1]) return brInst->getSuccessor(0);
              if (hasHazard[0] & hasHazard[1]) return nullptr;
              
              auto res = brdirMap.find(brOps);
              if (res != brdirMap.end()) {
                  if ((res->second).second) return brInst->getSuccessor(1);
                  else return brInst->getSuccessor(0);
              }
          }
      }
      for (BasicBlock *Succ : successors(BB)) {
          if (!containHazard(Succ)) return Succ;
      } // if no applicable heuristic, return the first hazard-free succ
      return nullptr; // if no any, return nullptr
    }

    private:
    // <op0, op1>: <heuristic priority (1:highest), branch to label1(false)/label2(true)>
    map<pair<Value*, Value*>, pair<int, bool> > brdirMap;
  };
}
char StaticTrace::StaticTracePass::ID = 0;
static RegisterPass<StaticTrace::StaticTracePass>
    C("static",
      "hazard avoidance + path selection", false, false);

namespace ProfileTrace {
    struct ProfileTracePass : public BaseTrace::BaseTracePass {
        static char ID;
        ProfileTracePass() : BaseTracePass(ID) {};

        virtual BasicBlock* predict(BasicBlock *BB, Function &F, PostDominatorTree &PDT, BranchProbabilityInfo &BPI) override {
            BasicBlock *bestSucc = nullptr;
            uint32_t maxProb = 0;
            for (BasicBlock *Succ : successors(BB)) {
                uint32_t prob = BPI.getEdgeProbability(BB, Succ).getNumerator();
                if (prob > maxProb) {
                    maxProb = prob;
                    bestSucc = Succ;
                }
            }
            if (maxProb >= thresProb) return bestSucc;
            else return nullptr;
        }

        private:
    };
}
char ProfileTrace::ProfileTracePass::ID = 0;
static RegisterPass<ProfileTrace::ProfileTracePass>
    P("profile",
      "use profile info", false, false);


namespace HazardProfileTrace {
    struct HazardProfileTracePass : public StaticTrace::StaticTracePass {
        static char ID;
        HazardProfileTracePass() : StaticTracePass(ID) {};

        virtual BasicBlock* predict(BasicBlock *BB, Function &F, PostDominatorTree &PDT, BranchProbabilityInfo &BPI) override {
            if (containHazard(BB)) return nullptr;
            Instruction *T = BB->getTerminator();
            if (BranchInst *brInst = dyn_cast<BranchInst>(T)) {
                if (brInst->isConditional()) { // conditional branch
                    Instruction *Icond = dyn_cast<Instruction>(brInst->getCondition());
                    pair<Value*, Value*> brOps = make_pair(Icond->getOperand(0), Icond->getOperand(1));
                    bool hasHazard[2] = {0, 0};
                    for (unsigned bridx = 0; bridx < 2; bridx++) {
                        BasicBlock *Succ = brInst->getSuccessor(bridx);
                        if (containHazard(Succ)) hasHazard[bridx] = 1;
                        /*for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                            if (PDT.dominates(&bb->front(), &Succ->front()))
                                if (containHazard(&(*bb))) hasHazard[bridx] = 1;
                        }*/
                    }
                    if (hasHazard[0] & !hasHazard[1]) return brInst->getSuccessor(1);
                    if (!hasHazard[0] & hasHazard[1]) return brInst->getSuccessor(0);
                    if (hasHazard[0] & hasHazard[1]) return nullptr;
                }
            }

            BasicBlock *bestSucc = nullptr;
            uint32_t maxProb = 0;
            for (BasicBlock *Succ : successors(BB)) {
                uint32_t prob = BPI.getEdgeProbability(BB, Succ).getNumerator();
                if (prob > maxProb) {
                    maxProb = prob;
                    bestSucc = Succ;
                }
            }
            if ((maxProb >= thresProb) & !containHazard(bestSucc)) return bestSucc;
            else return nullptr;
        }
    };
}
char HazardProfileTrace::HazardProfileTracePass::ID = 0;
static RegisterPass<HazardProfileTrace::HazardProfileTracePass>
    HP("hazardprofile",
      "testing inheritence", false, false);
