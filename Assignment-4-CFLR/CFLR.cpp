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
    // ---------- 步骤1：初始化工作表：加入所有原始终结符和已有非终结符边 ----------
    // 获取图的后继邻接表
    auto& succMap = graph->getSuccessorMap();
    // 遍历每个起点节点
    for (const auto& srcEntry : succMap) {
        unsigned src = srcEntry.first;  // 取出当前起点
        // 遍历该起点的所有边标签
        for (const auto& labelEntry : srcEntry.second) {
            EdgeLabel label = labelEntry.first;  // 取出当前边的标签
            // 遍历该标签下的所有终点，加入所有已有边，包含原始终结符与已有非终结符
            for (unsigned dst : labelEntry.second) {
                // 构造CFL可达性边对象
                CFLREdge edge(src, dst, label);
                // 将边加入工作表
                workList.push(edge);
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

        // 定义单符号产生式的映射表（from -> to）
        std::map<EdgeLabel, EdgeLabel> singleProdMap = {
            {Copy, VF},
            {CopyBar, VFBar}
        };
        // ========== 处理单符号产生式 A::=X ==========
        // 遍历映射表，统一处理所有单符号产生式
        for (const auto& entry : singleProdMap) {
            EdgeLabel from = entry.first;    // 产生式左侧（当前边应为 from）
            EdgeLabel to = entry.second;     // 产生式右侧（要产生的非终结符）
            if (X == from) {   // 判断当前边标签是否匹配
                // 先检查图中是否已存在 vi→(VF)vj 这条边
                if (!graph->hasEdge(vi, vj, to)) {
                    // 若不存在，添加新边到图中
                    graph->addEdge(vi, vj, to);
                    // 同时将新边加入工作表
                    workList.push(CFLREdge(vi, vj, to));
                }
            }
        }

        // 定义双符号产生式的映射表，按 (A, B, C), C ::= A B 
        std::vector<std::tuple<EdgeLabel, EdgeLabel, EdgeLabel>> BiProdMap = {
            {VFBar, AddrBar, PT},
            {Addr, VF, PTBar},
            {VF, VF, VF},
            {SV, Load, VF},
            {PV, Load, VF},
            {Store, VP, VF},
            {VFBar, VFBar, VFBar},
            {LoadBar, SVBar, VFBar},
            {LoadBar, VP, VFBar},
            {PV, StoreBar, VFBar},
            {LV, Load, VA},
            {VFBar, VA, VA},
            {VA, VF, VA},
            {Store, VA, SV},
            {VA, StoreBar, SVBar},
            {PTBar, VA, PV},
            {VA, PT, VP},
            {LoadBar, VA, LV}
        };
        // ========== 处理双符号产生式 A::=X Y（左结合） ==========
        // 如果当前边 X 等于规则的 A（左符号），则查找 vj 是否存在标签为 B 的后继边
        for (const auto& entry : BiProdMap) {
            EdgeLabel A = std::get<0>(entry);        // 规则左符号 A
            EdgeLabel B = std::get<1>(entry);        // 规则右符号 B
            EdgeLabel C = std::get<2>(entry);        // 产生出的非终结符 C (C ::= A B)
            if (X == A) {   // 判断当前边标签是否匹配为 A
                auto succIt = graph->getSuccessorMap().find(vj);
                if (succIt != graph->getSuccessorMap().end()) {
                    auto lblIt = succIt->second.find(B);
                    if (lblIt != succIt->second.end()) {
                        for (unsigned vk : lblIt->second) {
                            // 先检查图中是否已存在 vi→(C)vk 这条边
                            if (!graph->hasEdge(vi, vk, C)) {
                                // 若不存在，添加新边到图中
                                graph->addEdge(vi, vk, C);
                                // 同时将新边加入工作表
                                workList.push(CFLREdge(vi, vk, C));
                            }
                        }
                    }
                }
            }
        }

        // ========== 处理双符号产生式 A::=Y X（右结合） ==========
        // 如果当前边 X 等于规则的 B（右符号），则查找 vi 是否存在标签为 A 的前驱边
        for (const auto& entry : BiProdMap) {
            EdgeLabel A = std::get<0>(entry);        // 规则左符号 A
            EdgeLabel B = std::get<1>(entry);        // 规则右符号 B
            EdgeLabel C = std::get<2>(entry);        // 产生出的非终结符 C (C ::= A B)
            if (X == B) {   // 判断当前边标签是否匹配为 B（当前边是右符号）
                auto predIt = graph->getPredecessorMap().find(vi);
                if (predIt != graph->getPredecessorMap().end()) {
                    auto lblIt = predIt->second.find(A);
                    if (lblIt != predIt->second.end()) {
                        for (unsigned vk : lblIt->second) {
                            // 先检查图中是否已存在 vk→(C)vj 这条边
                            if (!graph->hasEdge(vk, vj, C)) {
                                // 若不存在，添加新边到图中
                                graph->addEdge(vk, vj, C);
                                // 将新边加入工作表
                                workList.push(CFLREdge(vk, vj, C));
                            }
                        }
                    }
                }
            }
        }
    }
}
