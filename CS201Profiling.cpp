/*
 * Authors: Name(s) <email(s)>
 *
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Dominators.h"
#include <map>
#include <vector>
#include <string>
#include <queue>
#include <stack>

using namespace std;
using namespace llvm;


namespace {
    //Plug-in printf 
    static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
        std::vector<Type*> printf_arg_types;
        printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
     
        FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
        Function *func = mod->getFunction("printf");
        if(!func)
            func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
        func->setCallingConv(CallingConv::C);
        return func;
    }

    struct CS201Profiling : public FunctionPass {
        static char ID;
        CS201Profiling() : FunctionPass(ID) {}

//Personal Definition
        class MyBasicBlock{
        public:
            MyBasicBlock(BasicBlock *b = NULL, int x = -1):bb(b), id(x){}
            BasicBlock *bb;
            int id;
        };
    //BasicBlock||Domination Used Definition
        vector<MyBasicBlock> bbVector;
        vector<vector<MyBasicBlock>> dominatorSet;  //All notes that domination
        vector<vector<MyBasicBlock>> dominatorTree; //Only immediate
        //vector<vector<int>> dominatorSet;
    //Loop Detect Definition
        vector<int> depthFirstOrdering;
        class Edge{
            public:
            Edge(MyBasicBlock a = MyBasicBlock(), MyBasicBlock b = MyBasicBlock()):u(a), v(b) {}
            MyBasicBlock u;
            MyBasicBlock v;
        };
        vector<Edge> backEdge;    
        vector<Edge> allEdge;
    //Count Frequency of BasicBlock, Control Flow Edge and Loop
        vector<int> bbCount;
//Hack Code Definition
        LLVMContext *Context;
        vector<GlobalVariable*> bbCounter;
        GlobalVariable *BasicBlockPrintfFormatStr = NULL;
        Function *printf_func = NULL;
    //BasicBloce Profiling
        class BasicBlockProfile{
            public:
            GlobalVariable *counter;
            GlobalVariable *printer;
            string name;
            Function *printf_func;
            Constant *basic_format_const;
            MyBasicBlock mbb;
        };
        vector<BasicBlockProfile> basicBlockProfile;
        BasicBlockProfile outputBlockProfile;
    //Edge profiling
        class MyEdgeBlock{
        public:
            MyEdgeBlock(GlobalVariable *a = NULL, GlobalVariable *b = NULL): counter(a), printer(b) 
            {
                printf_func = NULL;
                edge_format_const = NULL;
                newBB = NULL;
            }
            GlobalVariable *counter;
            GlobalVariable *printer;
            Edge edge;
            string name;
            Function *printf_func;
            Constant *edge_format_const;
            BasicBlock *newBB;
        };
        vector<MyEdgeBlock> edgeProfile;
        MyEdgeBlock outputEdgeBlockProfile;
    //Loop profile
        vector<vector<MyBasicBlock>> loopBlocks;
        vector<MyEdgeBlock> loopProfile;
        MyEdgeBlock outputLoopProfile;

        static void MyShow(string s){
            errs() << "\n------" << s << "------\n";
        }

//Test, get pred matrix
        void ShowPredList()
        {
        	for(int i = 0; i < (int)bbVector.size(); ++i)
	        {
	            errs() << "id-" << i << ": ";
	            for (auto j = pred_begin(bbVector[i].bb); j != pred_end(bbVector[i].bb); ++j)
        	    {
	                BasicBlock *bb = *j;
        	        errs() << GetId(bb) << " ";
        	    }
        	    errs() <<"\n";
        	}
        }

//GetDepthFirstVisitOrdering(); 
        vector<int> visitOrdering;
        void GetDepthFirstVisitOrdering(MyBasicBlock cur, bool mark[])
        {
            visitOrdering.push_back(cur.id);
            mark[cur.id] = true;
            //MyShow("currentID");
            //errs() << cur.id << "\n";
            for(auto it = succ_begin(cur.bb); it != succ_end(cur.bb); it++)
            {    
                MyBasicBlock next = MyBasicBlock((BasicBlock*)*it, GetId((BasicBlock*)*it));
                if(mark[next.id])
                    continue;
                GetDepthFirstVisitOrdering(next, mark);
                visitOrdering.push_back(cur.id); 
            }
        }

//GetDepthFirstOrdering();
        void GetDepthFirstOrdering()
        {
            bool mark[bbVector.size()];
            int counter = 0;
            memset(mark, 0, sizeof(mark));
            depthFirstOrdering = vector<int>(bbVector.size(), 0);
            for(int i = visitOrdering.size() - 1; i >= 0; i--)
            {
                if(!mark[visitOrdering[i]])
                {
                    mark[visitOrdering[i]] = true;
                    depthFirstOrdering[visitOrdering[i]] = counter++;
                }
            }
        }
//GetAllCFGEdge()
        void GetAllCFGEdge()
        {
            for(int i = 0; i < bbVector.size(); ++i)
            {
                for(auto it = succ_begin(bbVector[i].bb); it != succ_end(bbVector[i].bb); it++)
                {
                    BasicBlock *bbb = *it;
                    allEdge.push_back(Edge(bbVector[i], MyBasicBlock(bbb, GetId(bbb))));
                    //errs() << "Block " << bbVector[i].id << " to " << GetId(bbb) << "\n";
                }
            }
        }
//FindBackEdge()
//Match each edge in allEdge with depthFirstOrdering, to figure out all back edge.
        vector<Edge> FindBackEdge()
        {
            vector<Edge> temp;
            for(auto &edge : allEdge)
            {
                if(depthFirstOrdering[edge.u.id] > depthFirstOrdering[edge.v.id])
                {
                    //errs() << "Discover back edge: " << edge.u.id << " -> " << edge.v.id << "\n"; 
                    temp.push_back(edge);
                }   
            }
            return temp;
        }
//GetLoop
    // Insert element into loop
        void MyInsert(MyBasicBlock m, vector<int> &loop, stack<MyBasicBlock> &s)
        {
            bool flag = true;
            for(auto id:loop)
            {
                if(id == m.id)
                {
                    flag = false;
                    break;
                }
            }

            if(flag){
                loop.push_back(m.id);
                s.push(m);
            }
        }
    //Find BasicBlock according to id
        MyBasicBlock FindMyBasicBlock(int id)
        {
            for(auto &bb : bbVector)
            {
                if(bb.id == id)
                    return bb; 
            }
        }
    //Find out all the loop according to back edge.
        void GetLoop()
        {
            errs() << "\n\n";
            MyShow("Loop Information");
            for(auto &edge : backEdge)
            {
                vector<int> loop;
                stack<MyBasicBlock> s;
                loop.push_back(edge.v.id);
                MyInsert(edge.u, loop, s);
                while(!s.empty())
                {
                    MyBasicBlock cur = s.top();
                    s.pop();
                    for(auto it = pred_begin(cur.bb); it != pred_end(cur.bb); it++)
                    {
                        BasicBlock *bbb = *it;
                        MyInsert(MyBasicBlock(bbb, GetId(bbb)), loop, s);
                    }
                }

                //Store loop blocks
                vector<MyBasicBlock> temploop;
                for (auto id : loop){ 
                    MyBasicBlock temp = FindMyBasicBlock(id);
                    temploop.push_back(temp);
                }
                loopBlocks.push_back(temploop);

                //Output Loop information
                errs() << "Loop: ";
                for (auto id:loop)
                    errs() << id <<" ";
                errs() << "\n";
            }
            errs() << "\n\n";
        }

//Getid(BasicBlock)
//Get basicblock id according to basicblock
        int GetId(BasicBlock *b)
        {
            for(auto mbb : bbVector)
            {
                if (mbb.bb == b){
                    //errs() << "find id" << mbb.id << "\n";
                    return mbb.id;
                }
            }
            //errs() << "cannot find correct id !\n";
            return -1;
        }

//DDfs(current, dominator)
        //if there are bb has no paths, which doesn't go through p,  can reach start node. That means,
        //p dominates cur
        bool DDfs(MyBasicBlock cur, MyBasicBlock p, bool mark[])
        {
            if(cur.id == p.id || p.id == 0)	//Dominate itself and start note dominate all notes.
                return true;
            if(cur.id == 0)	//Reach start note, p do not dominate cur.
                return false;
            bool flag = true;
            for (auto next = pred_begin(cur.bb); flag && next != pred_end(cur.bb); next++)
            {
                //errs() << "inverse dfs search begin\n";
                BasicBlock *bbb = *next;
                int next_id = GetId(bbb);
                // if(next_id >= p.id)
                    // continue;
                if(mark[next_id])	continue;
                else mark[next_id] = 1;

                flag = DDfs(MyBasicBlock(bbb, next_id), p, mark);
            }
            return flag;
        }

//----------------------------------
        bool doInitialization(Module &M) {
            //MyShow("doInitialization begin");
            //MyShow("BasicBlock Information");
            int idCounter = 0;
            for(auto &func : M)
            {
                //if(func.getName() != "main")
                    errs() << "\nFunction " <<func.getName()<<" \n";
//Get Basicblock and give them id
                for(auto &bb : func)
                {
                    MyBasicBlock temp;
                    temp.id = idCounter++;
                    temp.bb = &bb;
                    //errs() << temp.id <<"\n";
                    bbVector.push_back(temp);
                }
                //Output BasicBlock information
                for(auto &bb : func)
                {
                    int id = GetId(&bb);
                    errs() << "BasicBlock\n" << "b" << id;
                    for(int j = 0; j < 40; j++)
                        errs() << " ";
                    if(pred_begin(&bb) != pred_end(&bb))
                    {
                        errs() << "; preds = ";
                        for(auto it = pred_begin(&bb); it != pred_end(&bb); ++it){
                            if(it != pred_begin(&bb))
                                errs() << ", ";
                            errs() << "%" << id;
                        }
                    }
                    errs() << "\n";
                    for(auto &I : bb){
                        errs() << I << "\n";
                    }
                    errs() << "\n";
                }
                errs() << "\n";
                //ShowPredList();
                //dominatorSet = vector<vector<int>>(bbVector.size(), vector<int>());
                dominatorSet = vector<vector<MyBasicBlock>>(bbVector.size(), vector<MyBasicBlock>());
                //errs() << "bbVector size" << (int)bbVector.size();
//Build domination set
//Get dominator tree
                for(int i = 0; i < (int)bbVector.size(); i++)
                    for(int j = 0; j <= i; ++j){
                        bool mark[bbVector.size()];
                        memset(mark, 0, sizeof(mark));
                        if(DDfs(bbVector[i], bbVector[j], mark))
                        {
                            dominatorSet[i].push_back(bbVector[j]);
                            //errs() << "i = " << i << " is dominated by j = " << j << "\n";
                        }
                    }
//Output domination tree information
                if(func.getName().equals("main") == false)
                    MyShow("Dominator Information");
                if(func.getName() != "main")
                for(int i = 0; i < (int)dominatorSet.size(); ++i)
                {
                    errs() << "dominator[" << i << "] = ";
                    for(auto &x : dominatorSet[i])
                    {
                        errs() << x.id << " ";
                    }
                    errs() << "\n";
                }
//Get back-edge
//Calculate depth first ordering
            if(func.getName().equals("main") == false){
                bool mark[bbVector.size()];
                memset(mark, 0, sizeof(mark));
                //MyShow("GetDepthFirstVisitOrdering");
                GetDepthFirstVisitOrdering(bbVector[0], mark);
                //MyShow("GetDepthFirstOrdering");
                GetDepthFirstOrdering();
                //MyShow("GetALLCFGEdge");
                GetAllCFGEdge();
//Find back edge
                //MyShow("FindBackEdge");
                backEdge = FindBackEdge();
//Get loop
                //MyShow("GetLoop");
                GetLoop();
                }
            }

            

//Hack code initialization
    //Initial Global Variable
            Context = &M.getContext();
            //bbCounter = vector<GlobalVariable*> (bbVector.size(), NULL);
            basicBlockProfile = vector<BasicBlockProfile>(bbVector.size());
            int tempCounter = 0;
            for(auto &bbp : basicBlockProfile)
            {
                bbp.mbb = bbVector[tempCounter++];
                bbp.name = "b" + to_string(bbp.mbb.id) + ": %d\n";
                bbp.basic_format_const = ConstantDataArray::getString(*Context, bbp.name);
                bbp.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false,GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), bbp.name.c_str());
                bbp.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), bbp.name.length() + 1), true, llvm::GlobalValue::PrivateLinkage, bbp.basic_format_const, "BasicBlockPrintfFormatStr");
                bbp.printf_func = printf_prototype(*Context, &M);
            }
            //Initialize "Basic Block Profiling:" output
            outputBlockProfile.name = "\nBasicBlock Profileing:\n";
            outputBlockProfile.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false,GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), outputBlockProfile.name.c_str());
            outputBlockProfile.basic_format_const = ConstantDataArray::getString(*Context, outputBlockProfile.name);
            outputBlockProfile.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), outputBlockProfile.name.length() + 1), true, llvm::GlobalValue::PrivateLinkage, outputBlockProfile.basic_format_const, "BasicBlockPrintfFormatStr");
            outputBlockProfile.printf_func = printf_prototype(*Context, &M);
            
//CFG edge profiling initialize 
            //Initialize new BB value
            for(auto &edge : allEdge)
            {
                MyEdgeBlock temp;
                temp.edge = edge;
                temp.name = "counterOfEdge" + to_string(edge.u.id) + "To" + to_string(edge.v.id);
                temp.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), temp.name.c_str()); 
                string pp = "";
                pp = to_string(edge.u.id) + " -> " + to_string(edge.v.id) + ": %d\n";
                temp.edge_format_const = ConstantDataArray::getString(*Context, pp.c_str());
                temp.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), pp.length()+1), true, llvm::GlobalValue::PrivateLinkage, temp.edge_format_const, "BasicBlockPrintfFormatStr");
                temp.printf_func = printf_prototype(*Context, &M);

                edgeProfile.push_back(temp); 
            }
            //Initialize "Edge Profiling:" output
            outputEdgeBlockProfile.name = "\nEdge Profiling:\n";
            outputEdgeBlockProfile.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), outputEdgeBlockProfile.name.c_str()); 
            outputEdgeBlockProfile.edge_format_const = ConstantDataArray::getString(*Context, outputEdgeBlockProfile.name.c_str());
            outputEdgeBlockProfile.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), outputEdgeBlockProfile.name.length()+1), true, llvm::GlobalValue::PrivateLinkage, outputEdgeBlockProfile.edge_format_const, "BasicBlockPrintfFormatStr");
            outputEdgeBlockProfile.printf_func = printf_prototype(*Context, &M);
            
            //Initialize "Loop Profiling" output
            outputLoopProfile.name = "\nLoop Profiling:\n";
            outputLoopProfile.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), outputLoopProfile.name.c_str()); 
            outputLoopProfile.edge_format_const = ConstantDataArray::getString(*Context, outputLoopProfile.name.c_str());
            outputLoopProfile.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), outputLoopProfile.name.length()+1), true, llvm::GlobalValue::PrivateLinkage, outputLoopProfile.edge_format_const, "BasicBlockPrintfFormatStr");
            outputLoopProfile.printf_func = printf_prototype(*Context, &M);
            
            //Initialize new BB value on each succ of loop entry
            for(int i = 0; i < loopBlocks.size(); ++i)
            {
                MyBasicBlock entry = loopBlocks[i][0];
                //MyShow(string("Found loop entry id is :: " + to_string(entry.id)));
                MyEdgeBlock temp;
                string loopIdLink = "";
                //MyShow(string("size!!!!!" + to_string(loopBlocks[i].size())));
                for(int j = 0; j < loopBlocks[i].size(); ++j)
                {  
                    MyBasicBlock mbb = loopBlocks[i][j];
                    loopIdLink += to_string(mbb.id);
                    loopIdLink += "_";
                }
                loopIdLink = loopIdLink.substr(0, loopIdLink.length()-1);
                temp.name = "Loop " + loopIdLink; 
                temp.counter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), temp.name.c_str());
                string pp = "Loop " + loopIdLink + " Count: %d\n";
                temp.edge_format_const = ConstantDataArray::getString(*Context, pp.c_str());
                temp.printer = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), pp.length()+1), true, llvm::GlobalValue::PrivateLinkage, temp.edge_format_const, "BasicBlockPrintfFormatStr");
                temp.printf_func = printf_prototype(*Context, &M);
                    
                loopProfile.push_back(temp);
            }

            //MyShow("doInitialization end");
            return false;
        }






        //----------------------------------
        bool doFinalization(Module &M) {
          return false;
        }




//Loop Pulg-in Function
        bool EdgeInLoop(Edge edge, MyEdgeBlock &mEB)
        {
            for(int i = 0; i < loopBlocks.size(); ++i)
            {
                MyBasicBlock entry = loopBlocks[i][0];
                if(edge.u.id != entry.id)
                    continue;

                for(int j = 0; j < loopBlocks[i].size(); ++j)
                {
                    if(edge.v.id == loopBlocks[i][j].id)
                    {
                        mEB = loopProfile[i];
                        return true;
                    }
                }
            }
            return false;
        }


        //----------------------------------
        bool runOnFunction(Function &F) override {
            //string functionName = "Function ";
            //functionName += F.getName();
            //MyShow(functionName);

            bbCount = vector<int>(bbVector.size());
            for(auto &BB : F)
            {
                // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
                if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { // major hack?
                    addLoopCount(BB, Context);
                    addFinalPrintf(BB, Context, outputBlockProfile.counter, outputBlockProfile.printer, outputBlockProfile.printf_func);
                    for(int i = 0; i < basicBlockProfile.size(); ++i){
                        addFinalPrintf(BB, Context, basicBlockProfile[i].counter, basicBlockProfile[i].printer, basicBlockProfile[i].printf_func);
                    }
                    //Add output Instructions at the end of Main Function 
                    addFinalPrintf(BB, Context, outputEdgeBlockProfile.counter, outputEdgeBlockProfile.printer, outputEdgeBlockProfile.printf_func);
                    for(int i = 0; i < edgeProfile.size(); ++i){
                        addFinalPrintf(BB, Context, edgeProfile[i].counter, edgeProfile[i].printer, edgeProfile[i].printf_func);
                     }
                    addFinalPrintf(BB, Context, outputLoopProfile.counter, outputLoopProfile.printer, outputLoopProfile.printf_func);
                    for(int i = 0; i < loopProfile.size(); ++i)
                    {
                        addFinalPrintf(BB, Context, loopProfile[i].counter, loopProfile[i].printer, loopProfile[i].printf_func);
                    }
                }
            }
//BasicBlcok instructions add
            runOnBasicBlock();
//CFG edge profiling
            //Code before insertion
            //MyShow("code before insertion");
            //for(auto &BB : F){
            //    for(auto &I : BB){
            //        errs() << I << "\n";
            //    }
            //    errs()<< "\n";
            //}
            //Insert New Edge BasicBlock
            //errs() << "totally number of edges\n"; 
            //MyShow(to_string(edgeProfile.size()));
            if(F.getName().equals("main") == false){
            for(auto &eB : edgeProfile)
            {
                //MyShow("Reday to create new block");
                //eB.newBB = BasicBlock::Create(*Context, "", &F, eB.edge.v.bb);
                eB.newBB = BasicBlock::Create(*Context, "", &F);
                //MyShow("Create new block done");
                //IRBuilder<> iRBuilder((eB.newBB)->getFirstInsertionPt());
                IRBuilder<> iRBuilder(eB.newBB);
                //MyShow("getFirstInsertionPt() Done");
                Value *loadAddr = iRBuilder.CreateLoad(eB.counter);
                Value *addAddr = iRBuilder.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);

               // MyEdgeBlock mEB;
               // if(EdgeInLoop(eB.edge, mEB)
                //{
                //    Value *tLoadAddr = iRBuilder.CreateLoad(mEB.counter);
                 //   Value *tAddAddr = iRBuilder.CreateAdd(tLoadAddr, loadAddr);
                //    iRBuilder.CreateStore(tAddAddr, mEB.counter);
               // }

                //MyShow("Create new instrctions");
                iRBuilder.CreateStore(addAddr, eB.counter);
                iRBuilder.CreateBr(eB.edge.v.bb);
                int idx = 0;
                //errs()<<"successor number of edge.u " << eB.edge.u.bb->getTerminator()->getNumSuccessors() << "\n";
                //errs()<<"successor number of newBB " << eB.newBB->getTerminator()->getNumSuccessors() << "\n";
                for(auto it = succ_begin(eB.edge.u.bb); it != succ_end(eB.edge.u.bb); it++){
                    if(*it == eB.edge.v.bb) break;
                    idx ++;
                }
                //errs() << "available successor number: " << idx << "\n";
                (eB.edge.u.bb)->getTerminator()->setSuccessor(idx,eB.newBB);
                idx = 0;
                //for(auto it = succ_begin(eB.newBB); it != succ_end(eB.newBB); it++){
                //    if(*it == eB.edge.v.bb) break;
                //    idx ++;
                //}
                //errs() << "available successor number: " << idx << "\n";
                //eB.newBB->getTerminator()->setSuccessor(idx, eB.edge.v.bb);
                }
            }
            //MyShow("Code after insertion");
            //Code after insertion
            //for(auto &BB : F){
            //    for(auto &I : BB){
            //        errs() << I << "\n";
            //    }
            //    errs()<< "\n";
            //}
//Loop profiling
            //if(F.getName().equals("main") == false)
            //{
            //   for(auto loP : loopProfile)
            //   {
            //       for(auto &lo : loP)
            //       {
            //           lo.newBB = BasicBlock::Create(*Context, "", &F);
            //           IRBuilder<> IRBuilder(lo.newBB);
            //           Value *loadAddr = IRBuilder.CreateLoad(lo.counter);
            //           Value *addAddr = iRBuilder.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
            //           iRBuilder.CreateStore(addAddr, lo.counter);
            //           iRBuilder.CreateBr(lo.edge.v.bb);
            //           int idx = 0;
            //       }
            //   }
            //

            return true;
        }

        bool runOnBasicBlock() {
            for(int i = 0; i < basicBlockProfile.size(); ++i){
                IRBuilder<> iRBuilder(basicBlockProfile[i].mbb.bb->getFirstInsertionPt());
                Value *loadAddr = iRBuilder.CreateLoad(basicBlockProfile[i].counter);
                Value *addAddr = iRBuilder.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
                iRBuilder.CreateStore(addAddr, basicBlockProfile[i].counter);
            }
            return true;
        }

        //----------------------------------
        //Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
        //For this, prepare the SCCGraph, and append to last BB?
        void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func) {
            IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
            std::vector<Constant*> indices;
            Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
            indices.push_back(zero);
            indices.push_back(zero);
            Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
             
            Value *bbc = builder.CreateLoad(bbCounter);
            CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
            call->setTailCall(false);
        }

        void addLoopCount(BasicBlock& BB, LLVMContext *Context) {
            IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
            
            for(auto &eP : edgeProfile)
            {
                MyEdgeBlock mEB;
                //MyShow("Find Match Edge in Loop");
                if(EdgeInLoop(eP.edge, mEB))
                {
                    //MyShow("create loop value store");
                    Value *loadAddr = builder.CreateLoad(eP.counter);
                    Value *tLoadAddr = builder.CreateLoad(mEB.counter);
                    Value *tAddAddr = builder.CreateAdd(tLoadAddr, loadAddr);
                    builder.CreateStore(tAddAddr, mEB.counter);
                }
            }
        }
    };
}

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);

