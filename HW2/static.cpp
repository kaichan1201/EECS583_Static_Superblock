//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
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
        if (i->isAtomic()) // sync instr
            return true;
        if (op=="store") { // ambiguous store
            Value *oper = i->getOperand(1); // get the store destination
            if (auto *constant = dyn_cast<Constant>(oper)) continue;
            else return true;
        }
        if (op=="ret") // subroutine return
            return true;
        if (op=="indirectbr") // indirect jump
            return true;
    }
    return false;
}

BasicBlock* staticPredict(BasicBlock *brBlock, Function &F, map<pair<Value*, Value*>, pair<int, bool> > &brdirMap) {
    
    // place these in trace formation pass and pass them here
    PostDominatorTree PDT = &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
    
    if (containHazard(brBlock)) return nullptr;
    TerminatorInst *T = brBlock->getTerminator();
    if (BranchInst *brInst = dyn_cast<BranchInst>(T)) {
        if (brInst->isConditional()) { // conditional branch
            Value *cond = Ibr->getCondition();
            Instruction *Icond = dyn_cast<Instruction>(cond);
            Value *op0 = Icond->getOperand(0);
            Value *op1 = Icond->getOperand(1);
            pair<Value*, Value*> brOps = make_pair(op0, op1);
            bool hasHazard[2] = {0, 0};
            for (unsigned bridx = 0; bridx < 2; bridx++) {
                BasicBlock *Succ = brInst->getSuccessor(bridx);
                if (containHazard(Succ)) hasHazard[bridx] = 1;
                Instruction::iterator iSucc = Succ->begin();
                for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                    Instruction::iterator ibb = bb->begin();
                    if (PDT->dominates(&(*ibb), &(*iSucc)))
                        if (containHazard(&(*bb))) hasHazard[bridx] = 1;
                }
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
    return brInst->getSuccessor(0); // if no applicable heuristic, return the first succ
}

void genBrdirMap(Module &M, map<pair<Value*, Value*>, pair<int, bool> > &brdirMap) {
        
    // place these in trace formation pass and pass them here
    map<pair<Value*, Value*>, pair<int, bool> > brdirMap; // branch direction map
    // <op0, op1>: <heuristic priority (1:highest), branch to label1(false)/label2(true)>
        
    for (Module::iterator f = M.begin(), e = M.end(); f != e; ++f) {
        PostDominatorTree PDT = &getAnalysis<PostDominatorTreeWrapperPass>(*f).getPostDomTree();
        for (Function::iterator bb = f->begin(), e = f->end(); bb != e; ++bb) {
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
                            for (Module::iterator fIt = M.begin(), END = M.end(); fIt != END; ++fIt) {
                                LoopInfo &LI = getAnalysis<LoopInfo>(*fIt);
                                for (LoopInfo::iterator lIt = LI.begin(), lEND = LI.end(); lIt != lEND; ++lIt) {
                                    BasicBlock *preHead = lIt->getLoopPreheader();
                                    if (preHead==Succ) inloopPrehead[bridx] = 1;
                                    vector<BasicBlock *> allBlocks = lIt->getBlocks();
                                    if (find(allBlocks.begin(), allBlocks.end(), Succ) != allBlocks.end())
                                        inloop[bridx] = 1;
                                }
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
                            BasicBlock *Succ = Ibr->getSuccessor(bridx);
                            Instruction::iterator iSucc = Succ->begin();
                            for (Function::iterator bIt = F.begin(), END = F.end(); bIt != END; ++bIt) {
                                Instruction::iterator ibIt = bIt->begin();
                                if (PDT->dominates(&(*ibIt), &(*iSucc))) {
                                    for (User *op1User : op1->users()) {
                                        if (Instruction *Iop1User = dyn_cast<Instruction>(op1User)) {
                                            BasicBlock *Iop1UserBlock = Iop1User->getParent();
                                            if (&(*bIt)==Iop1UserBlock) leadtouse[bridx] = 1;
                                        }
                                    }
                                    for (User *op2User : op2->users()) {
                                        if (Instruction *Iop2User = dyn_cast<Instruction>(op2User)) {
                                            BasicBlock *Iop2UserBlock = Iop2User->getParent();
                                            if (&(*bIt)==Iop2UserBlock) leadtouse[bridx] = 1;
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
}
