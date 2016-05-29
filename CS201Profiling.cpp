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
#include <vector>
#include <string>
#include <queue>
#include <stack>
#include <unordered_map>

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
    
    //Loop Detect Definition
        vector<int> depthFirstOrdering;
        class Edge{
            public:
            Edge(MyBasicBlock a = MyBasicBlock(), MyBasicBlock b = MyBasicBlock()):u(a), v(b) {}
            MyBasicBlock u;
            MyBasicBlock v;
        };
        
//Hack Code Definition
        Module *MM;
        LLVMContext *Context;
        //Used to store output information, which will be inserted at the end of main function
        class BasicOutputFormat{
        public:
        	GlobalVariable *counter;
        	GlobalVariable *printer;
        	string name;
        	Function *printf_func;
        	Constant *format_const;
            void MessageGenerate(string s, Module *MM, LLVMContext *Context){
                this->name = s;
                this->counter = new GlobalVariable(*MM, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), this->name.c_str());
                this->format_const = ConstantDataArray::getString(*Context, this->name);
                this->printer = new GlobalVariable(*MM, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), this->name.length() + 1), true, llvm::GlobalValue::PrivateLinkage, this->format_const, "BasicBlockPrintfFormatStr");
                this->printf_func = printf_prototype(*Context, MM);
                // return x;
            }
        };
    //BasicBloce Profiling Declare
        class BasicBlockProfile: public BasicOutputFormat{
        public:
            MyBasicBlock mbb;
        };
    //Edge profiling Declare
        class MyEdgeBlock: public BasicOutputFormat{
        public:
            Edge edge;
            //New insert block
            BasicBlock *newBB;
        };

    //Function Level Profile
        class FunctionProfile{
        public:
            int idCounter;
        //Used in "Example Instrumentation Output"
            //BasicBlock || Domination Used Definition
            vector<MyBasicBlock> bbVector;
            vector<vector<MyBasicBlock>> dominatorSet;  //All notes that domination

        //Used in "Example Output of Profiled Program"
            //BasicBloce Profiling Definition
            vector<BasicBlockProfile> basicBlockProfile;

            //Edge Profile
            vector<MyEdgeBlock> edgeProfile;

            //Loop profile 
            vector<vector<MyBasicBlock>> loopBlocks;
            vector<MyEdgeBlock> loopProfile;
            vector<Edge> backEdge;    
            vector<Edge> allEdge;

            //Instructions
            //Most of the functions below should be as the function member of FunctionProfile. 
            //However, I have another due =_=
        };
        //Record all functions
        vector<Function*> functionSet;
        //Get detail of each functions
        unordered_map<Function*, FunctionProfile> fP;


        static void MyShow(string s){
            errs() << "\n------" << s << "------\n";
        }

//GetDepthFirstVisitOrdering(); 
        vector<int> visitOrdering;
        void GetDepthFirstVisitOrdering(MyBasicBlock cur, bool mark[], FunctionProfile &tFP)
        {
            visitOrdering.push_back(cur.id);
            mark[cur.id] = true;
            for(auto it = succ_begin(cur.bb); it != succ_end(cur.bb); it++)
            {    
                MyBasicBlock next = MyBasicBlock((BasicBlock*)*it, GetId((BasicBlock*)*it, tFP));
                if(mark[next.id])
                    continue;
                GetDepthFirstVisitOrdering(next, mark, tFP);
                visitOrdering.push_back(cur.id); 
            }
        }

//GetDepthFirstOrdering();
        void GetDepthFirstOrdering(FunctionProfile &tFP)
        {
            bool mark[tFP.bbVector.size()];
            int counter = 0;
            memset(mark, 0, sizeof(mark));
            depthFirstOrdering = vector<int>(tFP.bbVector.size(), 0);
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
        void GetAllCFGEdge(FunctionProfile &tFP)
        {
            for(int i = 0; i < (int)tFP.bbVector.size(); ++i)
            {
                for(auto it = succ_begin(tFP.bbVector[i].bb); it != succ_end(tFP.bbVector[i].bb); it++)
                {
                    BasicBlock *bbb = *it;
                    tFP.allEdge.push_back(Edge(tFP.bbVector[i], MyBasicBlock(bbb, GetId(bbb, tFP))));
                }
            }
        }
//FindBackEdge()
//Match each edge in allEdge with depthFirstOrdering, to figure out all back edge.
        vector<Edge> FindBackEdge(FunctionProfile &tFP)
        {
            vector<Edge> temp;
            for(auto &edge : tFP.allEdge)
                if(depthFirstOrdering[edge.u.id] > depthFirstOrdering[edge.v.id])
                    temp.push_back(edge);
            return temp;
        }
//GetLoop
    // Insert element into loop
        void MyInsert(MyBasicBlock m, vector<int> &loop, stack<MyBasicBlock> &s)
        {
            bool flag = true;
            for(auto id:loop)
                if(id == m.id)
                {
                    flag = false;
                    break;
                }
            if(flag){
                loop.push_back(m.id);
                s.push(m);
            }
        }
    //Find BasicBlock according to id
        MyBasicBlock FindMyBasicBlock(int id, FunctionProfile &tFP)
        {
            for(auto &bb : tFP.bbVector)
            {
                if(bb.id == id)
                    return bb; 
            }
        }
    //Find out all the loop according to back edge.
        void GetLoop(FunctionProfile &tFP)
        {
            errs() << "\n\n";
            MyShow("Loop Information");
            for(auto &edge : tFP.backEdge)
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
                        MyInsert(MyBasicBlock(bbb, GetId(bbb, tFP)), loop, s);
                    }
                }

                //Store loop blocks
                vector<MyBasicBlock> temploop;
                for (auto id : loop){ 
                    MyBasicBlock temp = FindMyBasicBlock(id, tFP);
                    temploop.push_back(temp);
                }
                tFP.loopBlocks.push_back(temploop);

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
        int GetId(BasicBlock *b, FunctionProfile &tFP)
        {
            for(auto mbb : tFP.bbVector)
            {
                if (mbb.bb == b){
                    return mbb.id;
                }
            }
            //errs() << "cannot find correct id !\n";
            //A small midstake which should be repaired.
            //Mistake: This should be an error message. However, for those new created blocked, they don't have id and they don't stored in any profile either. 
            return -1;
        }

//DDfs(current, dominator)
        //if there are bb has no paths, which doesn't go through p,  can reach start node. That means,
        //p dominates cur
        bool DDfs(MyBasicBlock cur, MyBasicBlock p, bool mark[], FunctionProfile &tFP)
        {
            if(cur.id == p.id || p.id == 0)	//Dominate itself and start note dominate all notes.
                return true;
            if(cur.id == 0)	//Reach start note, p do not dominate cur.
                return false;
            bool flag = true;
            for (auto next = pred_begin(cur.bb); flag && next != pred_end(cur.bb); next++)
            {
                BasicBlock *bbb = *next;
                int next_id = GetId(bbb, tFP);
                if(mark[next_id])	continue;
                else mark[next_id] = 1;

                flag = DDfs(MyBasicBlock(bbb, next_id), p, mark, tFP);
            }
            return flag;
        }

//Output BasicBlock information
        void ShowBasicBlock(Function &func, FunctionProfile &tFP)
        {
            for(auto &bb : func)
            {
                int id = GetId(&bb, tFP);
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
        }

//----------------------------------
        bool doInitialization(Module &M) {
            MM = &M;//Store Module Information
            Context = &M.getContext();
            for(auto &func : M)
            {
                functionSet.push_back(&func);
                FunctionProfile tFP;
                tFP.idCounter = 0;

                errs() << "\nFunction " <<func.getName()<<" \n";
//Get Basicblock and give them id
                for(auto &bb : func)
                {
                    MyBasicBlock temp;
                    temp.id = tFP.idCounter++;
                    temp.bb = &bb;
                    tFP.bbVector.push_back(temp);
                }
                
                ShowBasicBlock(func, tFP);

                tFP.dominatorSet = vector<vector<MyBasicBlock>>(tFP.bbVector.size(), vector<MyBasicBlock>());
//Build domination set
//Get dominator tree
                for(int i = 0; i < (int)tFP.bbVector.size(); i++)
                    for(int j = 0; j <= i; ++j){
                        bool mark[tFP.bbVector.size()];
                        memset(mark, 0, sizeof(mark));
                        if(DDfs(tFP.bbVector[i], tFP.bbVector[j], mark, tFP))
                            tFP.dominatorSet[i].push_back(tFP.bbVector[j]);
                    }
//Output domination tree information
                if(func.getName().equals("main") == false)
                    MyShow("Dominator Information");
                if(func.getName() != "main")
                    for(int i = 0; i < (int)tFP.dominatorSet.size(); ++i)
                    {
                        errs() << "dominator[" << i << "] = ";
                        for(auto &x : tFP.dominatorSet[i])
                        {
                            errs() << x.id << " ";
                        }
                        errs() << "\n";
                    }
//Get back-edge
    //Calculate depth first ordering
                if(func.getName().equals("main") == false){
                    bool mark[tFP.bbVector.size()];
                    memset(mark, 0, sizeof(mark));
                    GetDepthFirstVisitOrdering(tFP.bbVector[0], mark, tFP);
                    GetDepthFirstOrdering(tFP);
                    GetAllCFGEdge(tFP);
    //Find back edge
                    tFP.backEdge = FindBackEdge(tFP);
    //Get loop
                    GetLoop(tFP);
                }       
                //Add current function profile to allFunctionProfile vector
                fP.insert(std::make_pair(&func, tFP));
            }

            for(int i = 0; i < fP.size(); ++i)
            {
                Function *func = functionSet[i];
                FunctionProfile &tFP = fP.at(func);
    //Hack code initialization
        //Initial Global Variable
                tFP.basicBlockProfile = vector<BasicBlockProfile>(tFP.bbVector.size());
                int tempCounter = 0;
                for(auto &bbp : tFP.basicBlockProfile)
                {
                    bbp.mbb = tFP.bbVector[tempCounter++];
                    bbp.MessageGenerate(string("b" + to_string(bbp.mbb.id) + ": %d  \n"), MM, Context);
                }
                       
    //CFG edge profiling initialize 
                //Initialize new BB value
                for(auto &edge : tFP.allEdge)
                {
                    MyEdgeBlock temp;
                    string ss = to_string(edge.u.id) + " -> " + to_string(edge.v.id) + ": %d\n";
                    temp.MessageGenerate(ss, MM, Context);
                    temp.edge = edge;
                    tFP.edgeProfile.push_back(temp); 
                }
                
                //Initialize new BB value on each succ of loop entry
                for(int i = 0; i < tFP.loopBlocks.size(); ++i)
                {
                    MyEdgeBlock temp;
                    string loopIdLink = "Loop ";
                    for(int j = 0; j < tFP.loopBlocks[i].size(); ++j)
                    {  
                        MyBasicBlock mbb = tFP.loopBlocks[i][j];
                        loopIdLink += to_string(mbb.id);
                        loopIdLink += "_";
                    }
                    loopIdLink = loopIdLink.substr(0, loopIdLink.length()-1);
                    loopIdLink += "Count: %d\n";
                    temp.MessageGenerate(loopIdLink, MM, Context);
                      
                    tFP.loopProfile.push_back(temp);
                }

            }
            return false;
        }
        

        bool doFinalization(Module &M) {
          return false;
        }




//Loop Pulg-in Function
//Figure out whether current edge is the successor of loop's entry
        bool EdgeInLoop(Edge edge, MyEdgeBlock &mEB, Function &F)
        {
            for(int i = 0; i < fP.at(&F).loopBlocks.size(); ++i)
            {
                MyBasicBlock entry = fP.at(&F).loopBlocks[i][0];
                if(edge.u.id != entry.id)
                    continue;

                for(int j = 0; j < fP.at(&F).loopBlocks[i].size(); ++j)
                {
                    if(edge.v.id == fP.at(&F).loopBlocks[i][j].id)
                    {
                        mEB = fP.at(&F).loopProfile[i];
                        return true;
                    }
                }
            }
            return false;
        }


        //----------------------------------
        bool runOnFunction(Function &F) override {
            for(auto &BB : F)
            {
                // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
                if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) {
                    for(auto &func : functionSet){
                        //Insert output information of each functions except main-function
                        if(func->getName() == "main") continue;
                        //Count the frequence of Loop by insert code into edges that belongs to the successors of each loop's entry
                        addLoopCount(BB, Context, *func);

                        //Output BasicBlock Profiling after running the program
                        BasicOutputFormat x;
                        x.MessageGenerate("\nBasic Block Profiling\n", MM, Context);
                        addFinalPrintf(BB, Context, x.counter, x.printer, x.printf_func);
                        for(int i = 0; i < fP.at(func).basicBlockProfile.size(); ++i)
                            addFinalPrintf(BB, Context, fP.at(func).basicBlockProfile[i].counter, fP.at(func).basicBlockProfile[i].printer, fP.at(func).basicBlockProfile[i].printf_func);

                        //Output Edge Profiling after running the program
                        x.MessageGenerate("\nEdge Profiling\n", MM, Context);
                        addFinalPrintf(BB, Context, x.counter, x.printer, x.printf_func);
                        for(int i = 0; i < fP.at(func).edgeProfile.size(); ++i)
                            addFinalPrintf(BB, Context, fP.at(func).edgeProfile[i].counter, fP.at(func).edgeProfile[i].printer, fP.at(func).edgeProfile[i].printf_func);

                        //Output Loop Profiling after running the program
                        x.MessageGenerate("\nLoop Profiling\n", MM, Context);
                        addFinalPrintf(BB, Context, x.counter, x.printer, x.printf_func);
                        for(int i = 0; i < fP.at(func).loopProfile.size(); ++i)
                            addFinalPrintf(BB, Context, fP.at(func).loopProfile[i].counter, fP.at(func).loopProfile[i].printer, fP.at(func).loopProfile[i].printf_func);
                    }
                }
            }
            
//BasicBlcok instructions add (hack code)
            runOnBasicBlock(F);
//Insert edge profiling hack code
            if(F.getName().equals("main") == false){
                for(auto &eB : fP.at(&F).edgeProfile)
                {
                    eB.newBB = BasicBlock::Create(*Context, "", &F);
                    IRBuilder<> iRBuilder(eB.newBB);
                    
                    Value *loadAddr = iRBuilder.CreateLoad(eB.counter);
                    Value *addAddr = iRBuilder.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
     
                    iRBuilder.CreateStore(addAddr, eB.counter);
                    iRBuilder.CreateBr(eB.edge.v.bb);
                    int idx = 0;
                    for(auto it = succ_begin(eB.edge.u.bb); it != succ_end(eB.edge.u.bb); it++){
                        if(*it == eB.edge.v.bb) break;
                        idx ++;
                    }
                    (eB.edge.u.bb)->getTerminator()->setSuccessor(idx,eB.newBB);
                    idx = 0;
                }
            }   
            return true;
        }

//BasicBlcok instructions add (hack code)
        bool runOnBasicBlock(Function &F) {
            if(F.getName() != "main")
                for(int i = 0; i < fP.at(&F).basicBlockProfile.size(); ++i){
                    IRBuilder<> iRBuilder(fP.at(&F).basicBlockProfile[i].mbb.bb->getFirstInsertionPt());
                    Value *loadAddr = iRBuilder.CreateLoad(fP.at(&F).basicBlockProfile[i].counter);
                    Value *addAddr = iRBuilder.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
                    iRBuilder.CreateStore(addAddr, fP.at(&F).basicBlockProfile[i].counter);
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

        void addLoopCount(BasicBlock& BB, LLVMContext *Context, Function &F) {
            IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
            
            for(auto &eP : fP.at(&F).edgeProfile)
            {
                MyEdgeBlock mEB;
                if(EdgeInLoop(eP.edge, mEB, F))
                {
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

