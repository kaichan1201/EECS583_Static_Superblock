//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"

#include "string"
#include <map>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;

bool containHazard(BasicBlock* bb) {
    for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
        std::string op = i->getOpcodeName();
        if (op=="call") // subroutine call
            return true;
        else if (op=="cmpxchg" | op=="atomicrmw" | op=="fence") // sync instr
            return true;
        else if (op=="store") { // ambiguous store
            Value *oper = i->getOperand(1); // get the store destination
            if (auto *constant = dyn_cast<Constant>(oper)) continue;
            else return true;
        else if (op=="ret") // subroutine return
            return true;
        else if (op=="indirectbr") // indirect jump
            return true;
    }
    return false;
}

BasicBlock* staticPredict(BasicBlock *brBlock, Function &F, PostDominatorTree &PDT) {
    /* place this in trace formation function pass and pass PDT here
    PostDominatorTree PDT = &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
    */
    if (containHazard(brBlock)) return nullptr;
    for (BasicBlock *Succ : successors(brBlock)) {
        if (containHazard(Succ)) return nullptr;
        Instruction::iterator iSucc = Succ->begin();
        for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
            Instruction::iterator ibb = bb->begin();
            if (PDT->dominates(&(*ibb), &(*iSucc)))
                if (containHazard(&(*bb))) return nullptr;
        }
    }
}

namespace Correctness {
struct FPLICMPass : public LoopPass {
  static char ID;
  FPLICMPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */

    BranchProbabilityInfo &bpi =
        getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    BlockFrequencyInfo &bfi =
        getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

    // Get preheader and all blocks
    BasicBlock *preHead = L->getLoopPreheader();
    vector<BasicBlock *> allBlocks = L->getBlocks();

    // Identify most likely path
    BasicBlock *bb = L->getHeader();
    vector<BasicBlock *> freqPath = {bb};
    BasicBlock *bestSucc = NULL;
    uint32_t thresProb = uint32_t((1u << 31) * 0.8);
    while (1) {
      uint32_t maxProb = 0;
      for (BasicBlock *Succ : successors(bb)) {
        uint32_t prob = bpi.getEdgeProbability(bb, Succ).getNumerator();
        if (prob > maxProb) {
          maxProb = prob;
          bestSucc = Succ;
        }
      }
      if (find(freqPath.begin(), freqPath.end(), bestSucc) != freqPath.end())
        break; // backedge
      if (find(allBlocks.begin(), allBlocks.end(), bestSucc) == allBlocks.end())
        break; // out of the loop
      if (maxProb >= thresProb) {
        freqPath.push_back(bestSucc);
        bb = bestSucc;
      } else
        break;
    }

    // Identify the infrequent path
    vector<BasicBlock *> infreqPath = allBlocks; // first get all blocks
    for (int i = 0; i < freqPath.size(); i++)
      infreqPath.erase(find(infreqPath.begin(), infreqPath.end(), freqPath[i]));
    errs() << "InfreqPath size: " << infreqPath.size() << "\n";

    // Find the qualified load-store dependencies
    set<LoadInst *> toHoist = {};
    for (int i = 0; i < infreqPath.size(); i++) {
      bb = infreqPath[i];
      for (BasicBlock::iterator ii = bb->begin(), e = bb->end(); ii != e;
           ++ii) {
        string op = ii->getOpcodeName();
        if (op == "store") {
          Value *oper = ii->getOperand(1); // get the store destination
          for (User *destSt : oper->users()) {
            if (Instruction *IDep = dyn_cast<Instruction>(destSt)) {
              BasicBlock *IDepBlock = IDep->getParent();
              bool IinfreqPath = (find(freqPath.begin(), freqPath.end(),
                                       IDepBlock) != freqPath.end());
              string Iop = IDep->getOpcodeName();
              bool Iisload = (Iop == "load");
              bool otherDepInFreq = false;
              for (User *srcLd : oper->users()) { // make sure there's no other
                                                  // dependency in the freq path
                if (Instruction *IOther = dyn_cast<Instruction>(srcLd)) {
                  string opOther = IOther->getOpcodeName();
                  if (opOther == "load")
                    continue; // load doesn't matter
                  if (IOther == IDep)
                    continue;
                  if (IOther == &(*ii))
                    continue;
                  BasicBlock *IOtherBlock = IOther->getParent();
                  if (find(freqPath.begin(), freqPath.end(), IOtherBlock) !=
                      freqPath.end())
                    otherDepInFreq = true;
                }
              }
              if (IinfreqPath & Iisload & ~otherDepInFreq) {
                LoadInst *ldDep = cast<LoadInst>(IDep);
                toHoist.insert(ldDep);
              }
            }
          }
        }
      }
    }

    // Hoist loads
    if (toHoist.size() != 0)
      Changed = true;
    vector<Instruction *> HoistList = {};
    for (LoadInst *ld : toHoist) {
      Instruction *ldHoist = ld->clone();
      ldHoist->insertBefore(
          preHead
              ->getTerminator()); // must hoist to before the last inst (branch)
      HoistList.push_back(ldHoist);
      errs() << "Hoist load: " << *ldHoist << "\n";
    }

    // Maintain SSA
    for (Instruction *IHoist : HoistList) {
      LoadInst *ldHoist = cast<LoadInst>(IHoist);
      AllocaInst *var =
          new AllocaInst(ldHoist->getType(), 0, nullptr, ldHoist->getAlign(),
                         "", preHead->getTerminator());
      StoreInst *st = new StoreInst(ldHoist, var, preHead->getTerminator());
      Value *toReplace = ldHoist->getOperand(0);
      toReplace->replaceUsesOutsideBlock(var, preHead);
    }

    /* *******Implementation Ends Here******* */

    return Changed;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<BranchProbabilityInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }

private:
  /// Little predicate that returns true if the specified basic block is in
  /// a subloop of the current one, not the current one itself.
  bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
    assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
    return LI->getLoopFor(BB) != CurLoop;
  }
};
} // end of namespace Correctness

char Correctness::FPLICMPass::ID = 0;
static RegisterPass<Correctness::FPLICMPass>
    X("fplicm-correctness",
      "Frequent Loop Invariant Code Motion for correctness test", false, false);

namespace Performance {
struct FPLICMPass : public LoopPass {
  static char ID;
  FPLICMPass() : LoopPass(ID) {}

  void DFS(Instruction *Icons, vector<Instruction *> *chain, Loop *L,
           vector<BasicBlock *> *freqPath, set<Instruction *> *almostInvar) {
    string op = Icons->getOpcodeName();
    bool arith = false;
    if (op == "add" | op == "sub" | op == "mul" | op == "udiv" | op == "sdiv" |
        op == "urem" | op == "shl" | op == "lshr" | op == "ashr" | op == "and" |
        op == "or" | op == "xor" | op == "icmp" | op == "srem" | op == "fadd" |
        op == "fsub" | op == "fmul" | op == "fdiv" | op == "frem" |
        op == "fcmp")
      arith = true;
    BasicBlock *consBlock = Icons->getParent();
    bool ConsinfreqPath = (find(freqPath->begin(), freqPath->end(),
                                consBlock) != freqPath->end());
    bool ConsOperisInvar = true;
    int Noper = Icons->getNumOperands();
    for (int i = 0; i < Noper; i++) {
      Value *oper = Icons->getOperand(i);
      if (~L->isLoopInvariant(oper))
        ConsOperisInvar = false;
      if (Instruction *Ioper = dyn_cast<Instruction>(oper)) {
        set<Instruction *>::iterator almostInvarIter;
        almostInvarIter = almostInvar->find(Ioper);
        if (almostInvarIter == almostInvar->end())
          ConsOperisInvar = false;
      }
    }
    if (ConsinfreqPath & ConsOperisInvar) {
      almostInvar->insert(Icons);
      chain->push_back(Icons);
      for (User *consumer : Icons->users()) {
        Instruction *Icons = cast<Instruction>(consumer);
        DFS(Icons, chain, L, freqPath, almostInvar);
      }
    } else
      chain->push_back(nullptr);
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */

    BranchProbabilityInfo &bpi =
        getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    BlockFrequencyInfo &bfi =
        getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

    // Get preheader and all blocks
    BasicBlock *preHead = L->getLoopPreheader();
    vector<BasicBlock *> allBlocks = L->getBlocks();

    // Identify most likely path
    BasicBlock *bb = L->getHeader();
    vector<BasicBlock *> freqPath = {bb};
    BasicBlock *bestSucc = NULL;
    uint32_t thresProb = uint32_t((1u << 31) * 0.8);
    while (1) {
      uint32_t maxProb = 0;
      for (BasicBlock *Succ : successors(bb)) {
        uint32_t prob = bpi.getEdgeProbability(bb, Succ).getNumerator();
        if (prob > maxProb) {
          maxProb = prob;
          bestSucc = Succ;
        }
      }
      if (find(freqPath.begin(), freqPath.end(), bestSucc) != freqPath.end())
        break; // backedge
      if (find(allBlocks.begin(), allBlocks.end(), bestSucc) == allBlocks.end())
        break; // out of the loop
      if (maxProb >= thresProb) {
        freqPath.push_back(bestSucc);
        bb = bestSucc;
      } else
        break;
    }

    // Identify the infrequent path
    vector<BasicBlock *> infreqPath = allBlocks; // first get all blocks
    for (int i = 0; i < freqPath.size(); i++)
      infreqPath.erase(find(infreqPath.begin(), infreqPath.end(), freqPath[i]));
    errs() << "InfreqPath size: " << infreqPath.size() << "\n";

    // Find the qualified load-store dependencies
    map<LoadInst *, vector<StoreInst *>> toHoist;
    map<LoadInst *, vector<StoreInst *>>::iterator toHoistIter;
    for (int i = 0; i < infreqPath.size(); i++) {
      bb = infreqPath[i];
      for (BasicBlock::iterator ii = bb->begin(), e = bb->end(); ii != e;
           ++ii) {
        string op = ii->getOpcodeName();
        if (op == "store") {
          Value *oper = ii->getOperand(1); // get the store destination
          for (User *destSt : oper->users()) {
            if (Instruction *IDep = dyn_cast<Instruction>(destSt)) {
              BasicBlock *IDepBlock = IDep->getParent();
              bool IinfreqPath = (find(freqPath.begin(), freqPath.end(),
                                       IDepBlock) != freqPath.end());
              string Iop = IDep->getOpcodeName();
              bool Iisload = (Iop == "load");
              bool otherDepInFreq = false;
              for (User *srcLd : oper->users()) { // make sure there's no other
                                                  // dependency in the freq path
                if (Instruction *IOther = dyn_cast<Instruction>(srcLd)) {
                  string opOther = IOther->getOpcodeName();
                  if (opOther == "load")
                    continue; // load doesn't matter
                  if (IOther == IDep)
                    continue;
                  if (IOther == &(*ii))
                    continue;
                  BasicBlock *IOtherBlock = IOther->getParent();
                  if (find(freqPath.begin(), freqPath.end(), IOtherBlock) !=
                      freqPath.end())
                    otherDepInFreq = true;
                }
              }
              if (IinfreqPath & Iisload & ~otherDepInFreq) {
                LoadInst *ldDep = cast<LoadInst>(IDep);
                StoreInst *stDep = cast<StoreInst>(&(*ii));
                toHoistIter = toHoist.find(ldDep);
                if (toHoistIter != toHoist.end())
                  toHoistIter->second.push_back(stDep);
                else {
                  vector<StoreInst *> stDepVec = {stDep};
                  toHoist.insert(
                      pair<LoadInst *, vector<StoreInst *>>(ldDep, stDepVec));
                }
              }
            }
          }
        }
      }
    }

    // Find the almost invariance chain
    map<LoadInst *, vector<Instruction *>> toHoistChain;
    map<LoadInst *, vector<Instruction *>>::iterator toHoistChainIter;
    set<Instruction *> almostInvar;
    for (toHoistIter = toHoist.begin(); toHoistIter != toHoist.end();
         toHoistIter++) {
      vector<Instruction *> chain;
      almostInvar.insert(toHoistIter->first);
      for (User *ldConsumer : toHoistIter->first->users()) {
        Instruction *Ildcons = cast<Instruction>(ldConsumer);
        DFS(Ildcons, &chain, L, &freqPath, &almostInvar);
      }
      toHoistChain.insert(
          pair<LoadInst *, vector<Instruction *>>(toHoistIter->first, chain));
    }

    // Hoist loads and the chain
    if (toHoist.size() != 0)
      Changed = true;
    vector<Instruction *> HoistList = {};
    for (toHoistIter = toHoist.begin(); toHoistIter != toHoist.end();
         toHoistIter++) {
      Instruction *ldHoist = toHoistIter->first->clone();
      ldHoist->insertBefore(
          preHead
              ->getTerminator()); // must hoist to before the last inst (branch)
      errs() << "Hoist load: " << *ldHoist << "\n";
      HoistList.push_back(ldHoist);
      /*LoadInst *IldHoist = cast<LoadInst>(ldHoist);
      auto search = toHoistChain.find(IldHoist);
      for (Instruction *aluHoist : search->second) {
        if (aluHoist != nullptr) {
          errs() << "Hoist alu: " << *aluHoist << "\n";
          aluHoist->insertBefore(preHead->getTerminator());
        }
      }*/
    }

    // Maintain SSA
    for (Instruction *IHoist : HoistList) {
      LoadInst *ldHoist = cast<LoadInst>(IHoist);
      AllocaInst *var =
          new AllocaInst(ldHoist->getType(), 0, nullptr, ldHoist->getAlign(),
                         "", preHead->getTerminator());
      StoreInst *st = new StoreInst(ldHoist, var, preHead->getTerminator());
      Value *toReplace = ldHoist->getOperand(0);
      toReplace->replaceUsesOutsideBlock(var, preHead);
    }

    /* *******Implementation Ends Here******* */

    return Changed;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<BranchProbabilityInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }

private:
  /// Little predicate that returns true if the specified basic block is in
  /// a subloop of the current one, not the current one itself.
  bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
    assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
    return LI->getLoopFor(BB) != CurLoop;
  }
};
} // end of namespace Performance

char Performance::FPLICMPass::ID = 0;
static RegisterPass<Performance::FPLICMPass>
    Y("fplicm-performance",
      "Frequent Loop Invariant Code Motion for performance test", false, false);
