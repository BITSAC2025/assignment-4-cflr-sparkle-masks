/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // TODO: complete this function. The implementations of graph and worklist are provided.
    //  You need to:
    //  1. implement the grammar production rules into code;
    //  2. implement the dynamic-programming CFL-reachability algorithm.
    //  You may need to add your new methods to 'CFLRGraph' and 'CFLR'.
    // ---------- 步骤1：初始化工作表：加入所有原始终结符边 ----------
    // 获取图的后继邻接表
    auto& succMap = graph->getSuccessorMap();
    // 遍历每个起点节点
    for (const auto& srcEntry : succMap) {
        unsigned src = srcEntry.first;  // 取出当前起点
        // 遍历该起点的所有边标签
        for (const auto& labelEntry : srcEntry.second) {
            EdgeLabel label = labelEntry.first;  // 取出当前边的标签
            // 仅筛选终结符边
            if (label == Addr || label == Copy || label == Store || label == Load || 
                label == AddrBar || label == LoadBar || label == StoreBar || label == CopyBar) {
                // 遍历该标签下的所有终点
                for (unsigned dst : labelEntry.second) {
                    // 构造CFL可达性边对象
                    CFLREdge edge(src, dst, label);
                    // 将边加入工作表
                    workList.push(edge);
                }
            }
        }
    }

    // ---------- 步骤2：处理空产生式 A::=ε ----------
    // 定义包含ε产生式的非终结符集合（即可以通过空字符串推导的非终结符）
    std::unordered_set<EdgeLabel> epsilonNonTerms = {VF, VFBar, VA}; 
    std::unordered_set<unsigned> allNodes;  // 用于存储图中所有节点
    // 收集图中所有节点：从后继邻接表和前驱邻接表中提取所有起点/终点
    for (const auto& entry : succMap) allNodes.insert(entry.first);
    for (const auto& entry : graph->getPredecessorMap()) allNodes.insert(entry.first);
    // 为每个节点添加自环边
    for (EdgeLabel nt : epsilonNonTerms) {
        for (unsigned v : allNodes) {
            CFLREdge selfLoop(v, v, nt);  // 构造自环边
            // 若该自环边未存在于图中，则添加到图和工作表中
            if (!graph->hasEdge(v, v, nt)) {
                graph->addEdge(v, v, nt);
                workList.push(selfLoop);
            }
        }
    }

    // ---------- 步骤3：循环处理工作表，应用文法产生式 ----------
    while (!workList.empty()) {
        // 从工作表头部弹出一条待处理的边
        CFLREdge current = workList.pop();
        // 拆解当前边的核心信息，为后续应用文法规则做准备
        unsigned vi = current.src;    // 当前边的起点（记为vi）
        EdgeLabel X = current.label;  // 当前边的标签（记为X）
        unsigned vj = current.dst;    // 当前边的终点（记为vj）

        // 定义单符号产生式的映射表
        std::map<EdgeLabel, EdgeLabel> singleProdMap = {
            {VF, Copy},
            {VFBar, CopyBar}
        };
        // ========== 处理单符号产生式 A::=X ==========
        // 遍历映射表，统一处理所有单符号产生式
        for (const auto& entry : singleProdMap) {
            EdgeLabel A = entry.first;    // 目标非终结符A
            EdgeLabel targetX = entry.second;   // 当前边的标签X
            if (X == targetX) {   // 判断当前边标签是否匹配
                // 先检查图中是否已存在 vi→(VF)vj 这条边
                if (!graph->hasEdge(vi, vj, A)) {
                    // 若不存在，添加新边到图中
                    graph->addEdge(vi, vj, A);
                    // 同时将新边加入工作表
                    workList.push(CFLREdge(vi, vj, A));
                }
                break;  // 匹配到一个后跳出循环，避免重复处理
            }
        }

        // 定义双符号产生式的映射表
        std::vector<std::tuple<EdgeLabel, EdgeLabel, EdgeLabel>> BiProdMap = {
            {PT,    VFBar,  Addr},
            {PTBar, Addr,   VF},
            {VF,    VF,     VF},
            {VF,    SV,     Load},
            {VF,    PV,     Load},
            {VF,    Store,  VP},
            {VFBar, VFBar,  VFBar},
            {VFBar, LoadBar,SV},
            {VFBar, LoadBar,VP},
            {VFBar, PV,     StoreBar},
            {VA,    LV,     Load},
            {VA,    VFBar,  VA},
            {VA,    VA,     VF},
            {SV,    Store,  VA},
            {SVBar, VA,     StoreBar},
            {PV,    PTBar,  VA},
            {VP,    VA,     PT},
            {LV,    LoadBar,VA}
        };
        // ========== 处理双符号产生式 A::=X Y（左结合） ==========
        // 遍历映射表，统一处理所有左结合双符号产生式
        for (const auto& entry : BiProdMap) {
            EdgeLabel A = std::get<0>(entry);        // 目标非终结符A
            EdgeLabel targetX = std::get<1>(entry);  // 当前边的标签X（左符号）
            EdgeLabel Y = std::get<2>(entry);        // 后继边的标签Y（右符号）
            if (X == targetX) {   // 判断当前边标签是否匹配
                auto& vjSucc = graph->getSuccessorMap()[vj];  // 获取当前边终点vj的后继边集合
                // 检查vj是否存在标签为Y的后继边
                if (vjSucc.count(Y)){
                    // 遍历所有vj→(Y)→vk的边，生成vi→(A)→vk的新边
                    for (unsigned vk : vjSucc[Y]) {
                        // 先检查图中是否已存在 vi→(A)vk 这条边
                        if (!graph->hasEdge(vi, vk, A)) {
                            // 若不存在，添加新边到图中
                            graph->addEdge(vi, vk, A);
                            // 同时将新边加入工作表
                            workList.push(CFLREdge(vi, vk, A));
                        }
                    }
                }
                break;  // 匹配到一个后跳出循环，避免重复处理
            }
        }

        // ========== 处理双符号产生式 A::=Y X（右结合） ==========
        // 遍历映射表，统一处理所有右结合双符号产生式
        for (const auto& entry : BiProdMap) {
            EdgeLabel A = std::get<0>(entry);        // 目标非终结符A
            EdgeLabel Y = std::get<1>(entry);        // 后继边的标签Y（左符号）
            EdgeLabel targetX = std::get<2>(entry);  // 当前边的标签X（右符号）
            if (X == targetX) {   // 判断当前边标签是否匹配
                auto& viPred = graph->getPredecessorMap()[vi];  // 获取当前边起点vi的前驱边集合
                // 检查vi是否存在标签为Y的前驱边
                if (viPred.count(Y)){
                    // 遍历所有vk→(Y)→vi的边，生成vk→(A)→vj的新边
                    for (unsigned vk : viPred[Y]) {
                        // 先检查图中是否已存在 vk→(A)vj 这条边
                        if (!graph->hasEdge(vk, vj, A)) {
                            // 若不存在，添加新边到图中
                            graph->addEdge(vk, vj, A);
                            // 将新边加入工作表
                            workList.push(CFLREdge(vk, vj, A));
                        }
                    }
                }
                break;  // 匹配到一个后跳出循环，避免重复处理
            }
        }
    }
}
