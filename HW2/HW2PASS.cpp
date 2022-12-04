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

namespace BaseTrace {
  struct BaseTracePass : public ModulePass {
    static char ID;
    BaseTracePass() : ModulePass(ID) {};
    BaseTracePass(char id): ModulePass(id) {};

    Trace GrowTrace(BasicBlock* seedBB, DominatorTree &DT) {
      std::vector<BasicBlock*> trace;
      trace.push_back(seedBB);
      BasicBlock *currBB = seedBB;
      while (1) {
        visited.insert(currBB);
        BasicBlock *likelyBB = predict(currBB);
        if (!likelyBB || visited.find(likelyBB) != visited.end()) {break;}
        if (DT.dominates(&likelyBB->front(), &currBB->front())) {break;}
        currBB = likelyBB;
      }
      return Trace(trace);
    }

    bool runOnModule(Module &M) override {

      prepare(M);

      for (Function &F : M) {
        LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
        DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();

        std::vector<Loop*> allLoops = FindAllLoops(LI);
        // TODO: sort the loops based on depth

        // create block list based on loop
        for (Loop* L : allLoops) {
          errs() << "\nLoop\n";
          for (BasicBlock* BB : L->getBlocksVector()) {
            if (visited.find(BB) != visited.end() && !inSubLoop(BB, L, &LI)) {
              traces.push_back(GrowTrace(BB, DT));
            }
            errs() << BB->getName() << '\n';
          }
        }

        errs() << "\nFunc\n";
        for (BasicBlock &BB : F) {
          if (visited.find(&BB) != visited.end()) {
            traces.push_back(GrowTrace(&BB, DT));
          }
          errs() << BB.getName() << '\n';
        }
      }

      // evaluation
      
      return false;
    }
    
    virtual void prepare(Module &M) {

    }

    virtual BasicBlock* predict(BasicBlock *BB) {
      return nullptr;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<BranchProbabilityInfoWrapperPass>();
      AU.addRequired<BlockFrequencyInfoWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<DominatorTreeWrapperPass>();
    }
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
      "testing inheritence", false, false);

namespace Child {
  struct ChildPass : public BaseTrace::BaseTracePass {
    static char ID;
    ChildPass() : BaseTracePass(ID) {};

  };
}
char Child::ChildPass::ID = 0;
static RegisterPass<Child::ChildPass>
    C("child",
      "testing inheritence", false, false);

/* A helper class that uses K as key and vector<V> as value */
template <class K, class V> class KeyValues {
public:
  typedef typename std::vector<V> Values;

  void addItem(K key, V dep) {
    if (_keyValues.find(key) == _keyValues.end())
      _keyValues[key] = Values();
    _keyValues[key].push_back(dep);
  }

  void removeItem(K key, V dep) {
    _keyValues[key].erase(std::remove(_keyValues[key].begin(), _keyValues[key].end(), dep), _keyValues[key].end());
    if (_keyValues[key].size() == 0)
      removeKey(key);
  }

  void removeKey(K key) { _keyValues.erase(key); }

  typename std::map<K, Values>::iterator begin() { return _keyValues.begin(); }
  typename std::map<K, Values>::iterator end() { return _keyValues.end(); }
  Values &operator[](K key) { return _keyValues[key]; }

private:
  typename std::map<K, Values> _keyValues;
};

namespace Correctness {
struct FPLICMPass : public LoopPass {
  static char ID;
  FPLICMPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */

    BranchProbabilityInfo &BPI =
        getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();

    BasicBlock *preheader = L->getLoopPreheader();
    BasicBlock *header = L->getHeader();

    std::set<BasicBlock *> frequentPath({header});
    BasicBlock *bb = header;
    while (1) { // assumption: there will always be a frequent path
      BasicBlock *next_bb = nullptr;
      for (auto succ : successors(&*bb)) {
        // errs() << bb->getName() << ' ' << succ->getName() << ' ' <<
        // BPI.getEdgeProbability(&*bb, succ) << '\n';
        if (BPI.getEdgeProbability(&*bb, succ) >= BranchProbability(8, 10)) {
          frequentPath.insert(succ);
          next_bb = succ;
        }
      }
      bb = next_bb;
      if (bb == header)
        break;
    }

    std::vector<BasicBlock *> allBlocks = L->getBlocks();
    std::set<BasicBlock *> infrequentPath;
    std::set_difference(allBlocks.begin(), allBlocks.end(),
                        frequentPath.begin(), frequentPath.end(),
                        std::inserter(infrequentPath, infrequentPath.end()));

    // find frequent loads and corresponding infrequent deps
    KeyValues<Instruction *, Instruction *> hoistDeps;
    for (auto freqBlock : frequentPath) {
      for (auto inst = freqBlock->begin(); inst != freqBlock->end(); inst++)
        if (inst->getOpcode() == Instruction::Load)
          for (auto U : inst->getOperand(0)->users()) // U is of type User*
            if (auto I = dyn_cast<Instruction>(U))
              if (I->getOpcode() == Instruction::Store) { 
                if (frequentPath.find(I->getParent()) != frequentPath.end()) {
                  hoistDeps.removeKey(cast<Instruction>(inst));
                  break;
                }
                if (infrequentPath.find(I->getParent()) !=
                    infrequentPath.end()) {
                  hoistDeps.addItem(cast<Instruction>(inst), I);
                }
              }
    }

    // find unique load targets
    KeyValues<Value *, Instruction *> regLoadMap;
    for (auto const &depsPair : hoistDeps) {
      Instruction *loadInst = depsPair.first;
      Value *loadTarget = loadInst->getOperand(0);
      regLoadMap.addItem(loadTarget, loadInst);
    }

    // hoist loads
    for (auto const &regLoadPair : regLoadMap) {
      Changed = true;
      Value *loadTarget = regLoadPair.first;
      std::vector<Instruction *> loadInsts = regLoadPair.second;

      for (auto const &loadInst : loadInsts) {
        if (loadInst ==
            loadInsts[0]) { // only hoist once for each unique target
          AllocaInst *var =
              new AllocaInst(loadInst->getType(), 0, nullptr,
                             dyn_cast<LoadInst>(loadInst)->getAlign(), "",
                             preheader->getTerminator());
          LoadInst *hoistLoadInst = new LoadInst(
              loadInst->getType(), loadTarget, "", preheader->getTerminator());
          StoreInst *st =
              new StoreInst(hoistLoadInst, var, preheader->getTerminator());
          loadTarget->replaceUsesOutsideBlock(var, preheader);
        }
        for (auto const &depInst : hoistDeps[loadInst]) { // add fix-up code
          // Do nothing if only hoist load
        }
      }
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

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */

    BranchProbabilityInfo &BPI =
        getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

    // only optimize the inner-most loop
    for (auto const& block : L->getBlocks())
      if (inSubLoop(block, L, &LI)) return Changed;

    BasicBlock *preheader = L->getLoopPreheader();
    BasicBlock *header = L->getHeader();

    std::set<BasicBlock *> frequentPath({header});
    BasicBlock *bb = header;
    while (1) { // assumption: there will always be a frequent path
      BasicBlock *next_bb = nullptr;
      for (auto succ : successors(&*bb)) {
        if (BPI.getEdgeProbability(&*bb, succ) >= BranchProbability(8, 10)) {
          frequentPath.insert(succ);
          next_bb = succ;
        }
      }
      bb = next_bb;
      if (bb == header) break;
    }

    std::vector<BasicBlock *> allBlocks = L->getBlocks();
    std::set<BasicBlock *> infrequentPath;
    std::set_difference(allBlocks.begin(), allBlocks.end(),
                        frequentPath.begin(), frequentPath.end(),
                        std::inserter(infrequentPath, infrequentPath.end()));

    // find frequent loads and corresponding infrequent deps
    KeyValues<Instruction *, Instruction *> hoistDeps;
    for (auto freqBlock : frequentPath) {
      for (auto inst = freqBlock->begin(); inst != freqBlock->end(); inst++)
        if (inst->getOpcode() == Instruction::Load)
          for (auto U : inst->getOperand(0)->users()) // U is of type User*
            if (auto I = dyn_cast<Instruction>(U))
              if (I->getOpcode() == Instruction::Store) { 
                if (frequentPath.find(I->getParent()) != frequentPath.end()) {
                  hoistDeps.removeKey(cast<Instruction>(inst));
                  break;
                }
                if (infrequentPath.find(I->getParent()) !=
                    infrequentPath.end()) {
                  hoistDeps.addItem(cast<Instruction>(inst), I);
                }
              }
    }

    // Find load chain (instructions following load)
    KeyValues<Instruction*, Instruction*> loadChains;
    for (auto const &depsPair : hoistDeps) {
      Instruction *loadInst = depsPair.first;
      std::set<Value*> almostInvariants = {loadInst->getOperand(0), loadInst};
      
      // initialize queue
      std::deque<Instruction*> consumers_q;
      for (auto U : loadInst->users())
          if (auto I = dyn_cast<Instruction>(U))
            consumers_q.push_back(I);

      while (consumers_q.size() > 0) {
        Instruction *consumerInst = consumers_q[0];
        consumers_q.pop_front();

        if (frequentPath.find(consumerInst->getParent()) == frequentPath.end()) continue;
        if (consumerInst->getOpcode() == Instruction::Store) continue;

        bool isInvariantInst = true;
        for (auto it=consumerInst->op_begin(); it!=consumerInst->op_end(); it++) {
          Value *operand = cast<Value>(it);
          if (!L->isLoopInvariant(operand) && almostInvariants.find(operand) == almostInvariants.end()) {
            isInvariantInst = false;
            break;
          }
        }
        if (!isInvariantInst) continue;

        loadChains.addItem(loadInst, consumerInst);
        almostInvariants.insert(consumerInst);

        for (auto U : consumerInst->users())
          if (auto I = dyn_cast<Instruction>(U))
            consumers_q.push_back(I);
      }
    }

    for (auto const& loadChainPair : loadChains) {
      Instruction* loadInst = loadChainPair.first;
      std::vector<Instruction*> loadChain = loadChainPair.second;
      errs() << "Load chain for " << *loadChainPair.first << '\n';
      for (auto inst : loadChain)
        errs() << *inst << '\n';
      errs() << '\n';
    }

    // hoist 
    for (auto const &hoistDepPair : hoistDeps) {
      // errs() << *preheader << '\n';
      Changed = true;
      Instruction* loadInst = hoistDepPair.first;
      std::vector<Instruction*> loadChain = loadChains[loadInst];
      
      AllocaInst *var = new AllocaInst(loadChain.back()->getType(), 0, nullptr, cast<LoadInst>(loadInst)->getAlign(), "", preheader->getTerminator());
      StoreInst *st = new StoreInst(loadChain.back(), var, preheader->getTerminator());
      // create a new load that loads var
      LoadInst *replaceLoad = new LoadInst(
              loadChain.back()->getType(), var, "", loadChain.back()->getNextNode());
      
      // errs() << *preheader << '\n' << "Load block: " << *replaceLoad->getParent() << '\n';

      loadInst->moveBefore(var);  // move load to preheader (before var)
      // move the load chain to preheader (before var)
      for (auto const &inst : loadChain) {
        inst->moveBefore(var);
      }
      
      loadChain.back()->replaceUsesOutsideBlock(replaceLoad, preheader);

      // errs() << "After change: \n";
      // errs() << *preheader << '\n' << "Load block: " << *replaceLoad->getParent() << '\n';

      for (auto const &depInst : hoistDeps[loadInst]) { // add fix-up code
        // errs() << "\nStore block: " << *depInst->getParent() << '\n';
        ValueToValueMapTy vmap;
        for (auto const &inst : loadChain) {
          Instruction* newInst = inst->clone();

          // remap the load instructions
          for (auto it=newInst->op_begin(); it!=newInst->op_end(); it++) {
            if (*it == loadInst){
              // errs() << "match\n change to " << *depInst->getOperand(0) << '\n';
              *it = depInst->getOperand(0);  // depInst is store
            }
          }
          newInst->insertBefore(depInst);
          vmap[inst] = newInst;
          RemapInstruction(newInst, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
          if (inst == loadChain.back()) {
            StoreInst *newSt = new StoreInst(newInst, var, depInst);
            // errs() << "\nAfter change:\nStore block: " << *newSt->getParent() << '\n';
          }
        }        
      }

      // TODO: fix bug here
      // for (auto const &depInst : hoistDeps[loadInst])
      //   depInst->eraseFromParent();
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
