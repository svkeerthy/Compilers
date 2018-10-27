#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/User.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include <random>
using namespace llvm;


namespace{
	struct Flattening : public FunctionPass{

		static char ID;
		Flattening():FunctionPass(ID){}

		void getAnalysisUsage(AnalysisUsage &AU) const{
			AU.addRequired<LoopInfoWrapperPass>();
			AU.addRequired<DominatorTreeWrapperPass>();
		}

		static BasicBlock * createSwitchBlock(Function * F,SmallVector<Value *,5> randInstructions ,SmallVector<BasicBlock * , 10> Blocks , BasicBlock * HB,SmallVector<DominatorTree::UpdateType , 10> &Updates){
/*  %call = call i64 @time(i64* null) #2
  %conv = trunc i64 %call to i32
  call void @srand(i32 %conv) #2
  %call1 = call i32 @rand() #2
*/
			BasicBlock * BB = BasicBlock::Create(F->getContext(),"Switch",F);
			for (unsigned i=0;i<randInstructions.size();i++){
				BB->getInstList().push_back((Instruction *) randInstructions[i]);
			}

			SwitchInst * SW = SwitchInst::Create(randInstructions[4],BB,4,BB);
			SmallVector<ConstantInt * , 5> constants;
			for (int i=0;i<4;i++){

				constants.push_back(ConstantInt::get( IntegerType::get(F->getContext() , 32) ,i , false));
			}

			for (int i=0;i<3;i++){
				SW->addCase(constants[i],Blocks[i]);
				Updates.push_back({DominatorTree::Insert,BB,Blocks[i]});
		
			}
			//*randomValue = *rem;
			SW->addCase(constants[3],HB);
			Updates.push_back({DominatorTree::Insert,BB,HB});
			BB->dump();
			return BB;
		}

		static BasicBlock * createPreBlock(Function * F , Value * random , int key , BasicBlock * label1 ,BasicBlock * label2 , BasicBlock * prevBlock ){
		 
    		BasicBlock * preBlock = BasicBlock::Create(F->getContext(),Twine(".pre"+label2->getName()),F) ;
    		PHINode * phi = PHINode::Create(Type::getInt32Ty(F->getContext()),0);
     		phi->addIncoming(Constant::getIntegerValue(Type::getInt32Ty(F->getContext()),APInt(32,-1)) , prevBlock);
            Instruction * cmpInst = new ICmpInst(CmpInst::ICMP_EQ,(Value *)phi , random);
            preBlock->getInstList().push_back(phi);
            preBlock->getInstList().push_back(cmpInst);
   			preBlock->getInstList().push_back(BranchInst::Create(label1,label2,cmpInst)) ;
   			//preBlock->dump();
   			return preBlock ;
		
		}


        bool runOnFunction(Function& F) override {
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            bool check = false;
            for (Loop *L : LI){
                check = changeLoop(L);
            }
            return check;

        }

		bool changeLoop(Loop *L) {
			// Loop is currently not the outermost loop
			if (L->getSubLoops().size()>0){
				dbgs()<<"Hi";
				return false;
			}

			BasicBlock * HeaderBlock = L->getHeader();
			BasicBlock * Latch = L->getLoopLatch();
			Function * F = HeaderBlock->getParent();
			SmallVector<DominatorTree::UpdateType,10> Updates;

			Constant * randFunc = F->getParent()->getOrInsertFunction("rand",FunctionType::get(Type::getInt32Ty(F->getContext()),false));
			Constant * timeFunc = F->getParent()->getOrInsertFunction("time", FunctionType::get ( Type::getInt64Ty ( F->getContext() ) ,ArrayRef<Type*>( Type::getInt64PtrTy( F->getContext() ) ), false));
			Constant * srandFunc = F->getParent()->getOrInsertFunction("srand", FunctionType::get( Type::getVoidTy (F->getContext() ), ArrayRef<Type*>(Type::getInt32Ty(F->getContext())),false));
			SmallVector<Value * ,5> RandInstructions;
			RandInstructions.push_back((Value *) CallInst::Create( (Value *)timeFunc , ArrayRef<Value *>( (Value *)ConstantPointerNull::get(Type::getInt64PtrTy(F->getContext()))) ,"timeCall"));
			RandInstructions.push_back((Value *) new TruncInst((Value *) RandInstructions[0],Type::getInt32Ty(F->getContext()),"truncTime"));
			RandInstructions.push_back((Value *) CallInst::Create((Value *)srandFunc,ArrayRef<Value *>(RandInstructions[1])));
			RandInstructions.push_back((Value *) CallInst::Create((Value *)randFunc,ArrayRef<Value *>(),"randCall"));
			RandInstructions.push_back((Value *) BinaryOperator::Create(Instruction::SRem,RandInstructions[3],(Value *)ConstantInt::get(IntegerType::get(F->getContext(),32),4,false),"randomNumber"));
			
			// auto &DT  = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
			// LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			//LI.erase(L);			
			dbgs() <<"hello";
			//LI.removeLoop(L);
			SmallVector<BasicBlock * , 10> Body;
			for (unsigned i = 0 ; i< L->getBlocks().size() ; i++){
				if (L->getBlocks()[i]!=HeaderBlock && L->getBlocks()[i]!=Latch){
					Body.push_back(L->getBlocks()[i]);
				}
			}
			

			BranchInst * headerBranch=dyn_cast<BranchInst>(HeaderBlock->getTerminator());
			BasicBlock * endBlock = headerBranch->getSuccessor(1);
			BasicBlock * PreHeader = L->getLoopPreheader();
					
			dbgs() << "creating New blocks\n";
			SmallVector<BasicBlock * , 10 > NewBlocks;
			
			NewBlocks.push_back(createPreBlock(F,RandInstructions[4],0,HeaderBlock,Body[0],HeaderBlock) );
			NewBlocks.push_back(createPreBlock(F,RandInstructions[4],1,HeaderBlock,Latch,Body[0]));
			NewBlocks.push_back(createPreBlock(F,RandInstructions[4],2,HeaderBlock,endBlock,HeaderBlock));
			NewBlocks.push_back(createSwitchBlock(F,RandInstructions,NewBlocks,HeaderBlock,Updates));
			//NewBlocks[3]

			AlterPreHeader(PreHeader,NewBlocks[3],HeaderBlock);
			AlterHeaderBlock(HeaderBlock,NewBlocks[0],Body[0],endBlock,NewBlocks[2]);
			AlterBody(Body,Latch,NewBlocks[1]);
			PreHeader->dump();
			// Updates.push_back({DominatorTree::Insert,NewBlocks[0],Body[0]});
			// Updates.push_back({DominatorTree::Insert,NewBlocks[1],Latch});
			// Updates.push_back({DominatorTree::Insert,NewBlocks[2],endBlock});
			// Updates.push_back({DominatorTree::Insert,NewBlocks[0],HeaderBlock});
			// Updates.push_back({DominatorTree::Insert,NewBlocks[1],HeaderBlock});
			// Updates.push_back({DominatorTree::Insert,NewBlocks[2],HeaderBlock});
			// Updates.push_back({DominatorTree::Insert,PreHeader,NewBlocks[3]});
			// Updates.push_back({DominatorTree::Delete,HeaderBlock,Body[0]});
			// Updates.push_back({DominatorTree::Delete,HeaderBlock,endBlock});
			// Updates.push_back({DominatorTree::Delete,PreHeader,HeaderBlock});

			// DT.applyUpdates(Updates);


			for (int i= 0 ;i<3;i++){
				for (Instruction &I : *NewBlocks[i] ){
					if ( auto * ph = dyn_cast<PHINode>(&I)){
						ph->addIncoming(RandInstructions[4],NewBlocks[3]);

					}
				}
				NewBlocks[i]->dump();
			}
			F->viewCFG();

			// DT.viewGraph();
			// L->removeBlockFromLoop(HeaderBlock);
			// dbgs()<<"he";
			// L->removeBlockFromLoop(Latch);
			// dbgs()<<"he";
			// L->removeBlockFromLoop(PreHeader);
			// dbgs()<<"he";
			// L->removeBlockFromLoop(Body[0]);
			// for (LoopInfo::iterator i = LI.begin();i!=LI.end();i++){
			// 	if (*i == L){
			// 		LI.removeLoop(i);
			// 	}
			// }
			//LI.removeLoop(L);
			return true;

		}
		void AlterPreHeader(BasicBlock * preHeader, BasicBlock * switchBlock , BasicBlock * headerBlock){
			auto * branch = dyn_cast<BranchInst>(preHeader->getTerminator());
			if (branch -> isConditional()){
				if (branch->getSuccessor(0)== headerBlock){
					branch->setSuccessor(0,switchBlock);
				}
				else if (branch->getSuccessor(1) == headerBlock){
					branch->setSuccessor(1,switchBlock);
				}
			}
			else if (branch->isUnconditional()){
				if (branch->getSuccessor(0)==headerBlock){
					branch->setSuccessor(0,switchBlock);
				}
			}

		}

		void AlterHeaderBlock(BasicBlock * headerBlock , BasicBlock * preBody , BasicBlock * Body , BasicBlock * endBlock , BasicBlock * preEnd){
			auto * branch = dyn_cast<BranchInst>(headerBlock->getTerminator());
			if (branch->isConditional()){
				if (branch->getSuccessor(0) == Body){
					branch->setSuccessor(0,preBody);
					if (branch -> getSuccessor(1) == endBlock){
						branch -> setSuccessor(1,preEnd);
					}
				}
				else if (branch->getSuccessor(1) == Body){
					branch->setSuccessor(1,preBody);
					if (branch->getSuccessor(0)==endBlock){
						branch -> setSuccessor(0,preEnd);
					}
				}

			}
			else if (branch->isUnconditional()){
				if (branch->getSuccessor(0)==Body){
					branch->setSuccessor(0,preBody);
				}
			}
		}

		void AlterBody(SmallVector<BasicBlock * , 10> Body , BasicBlock * Latch , BasicBlock * preLatch ){
			for (unsigned i=0;i<Body.size();i++){
				if (BranchInst * branch = dyn_cast<BranchInst>(Body[i]->getTerminator())){
					if(branch->isConditional()){
						if (branch->getSuccessor(0) == Latch){
							branch->setSuccessor(0, preLatch);
							// Updates.push_back({DominatorTree::Delete,Body[i],Latch});
							// Updates.push_back({DominatorTree::Insert,Body[i],preLatch});
						}
						if (branch->getSuccessor(1) == Latch){
							branch->setSuccessor(0 , preLatch);
							// Updates.push_back({DominatorTree::Delete,Body[i],Latch});
							// Updates.push_back({DominatorTree::Insert,Body[i],preLatch});
						}
					}
					else if  (branch->isUnconditional()){
						if (branch->getSuccessor(0) == Latch){
							branch->setSuccessor(0,preLatch);
							// Updates.push_back({DominatorTree::Delete,Body[i],Latch});
							// Updates.push_back({DominatorTree::Insert,Body[i],preLatch});
						}
					}
				}


			}


		}


	};


}

char Flattening::ID = '1';
static RegisterPass<Flattening> Hi("flatten","Control flow flattening");
