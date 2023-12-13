#ifndef BSCC_H
#define BSCC_H

#include <deque>
#include<list>
#include<stack>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "petriTranslation.h"
#include "reachability.h"
#include "bdd_utilities.h"
#include "scc.h"
#include "tgr.h"
#include "deadlock.h"

using sylvan::Bdd;
using sylvan::BddSet;

SccResult chainAlgBottomAdvanced(const Graph &fullGraph);
SccResult chainAlgBottomSpecialFWD(const Graph &fullGraph);

SccResult chainAlgBottomSingleRecCall(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecSpecialFWD(const Graph &fullGraph);

SccResult chainAlgBottomSingleRecForwardLoop(const Graph &fullGraph);
SccResult chainAlgBottomForwardLoop(const Graph &fullGraph);

SccResult chainAlgBottomSingleRecCallCumulative(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecCallExtra(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecCallSwitch(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecCallSwitchAndBasin(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecCallInitState(const Graph &initGraph);

SccResult chainAlgBottomApproxPick(const Graph &fullGraph);

SccResult xbAlgBottomApproxPick(const Graph &fullGraph);




void printCube(BddSet cube);
void printRelation(Relation rel);
void printRelationMatrix(const Graph &graph);

template<class ReachType>
SccResult xieBeerelBottom(const Graph &fullGraph) {
  int symbolicSteps = 0;
  int recCalls = 0;

  std::list<Bdd> bsccList = {};
  //Return if graph is empty
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(bsccList, symbolicSteps);
  }

  //ITGR Testing:

  std::pair<Graph, int> reducedGraph = ITGR(fullGraph);
  symbolicSteps += reducedGraph.second;
  const Bdd allNodes = reducedGraph.first.nodes;
  const BddSet fullCube = reducedGraph.first.cube;
  const std::deque<Relation> relationDeque = reducedGraph.first.relations;
  //End ITGR


  //Normal code
  // const Bdd allNodes = fullGraph.nodes;
  // const BddSet fullCube = fullGraph.cube;
  // const std::deque<Relation> relationDeque = fullGraph.relations;
  //End Normal code

  //Deadlock detection
  /*std::pair<SccResult, Graph> dl = deadlockRemoval(fullGraph);
  symbolicSteps += dl.first.symbolicSteps;
  for(Bdd bs : dl.first.sccs){
    bsccList.push_back(bs);
  }
  const Bdd allNodes = dl.second.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;
  std::cout << ";" << bsccList.size();
  if(allNodes == leaf_false()) {
    std::cout << ";" << recCalls;
    return createSccResult(bsccList, symbolicSteps);
  }*/
  //Deadlock detection end

  //callstack used to emulate recursive calls
  std::stack<Bdd> callStack;
  callStack.push(allNodes);

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  //The type of reachability used - relationUnion or saturation
  ReachType reach;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet;
    Bdd backwardSet;

    workingGraph.nodes = nodeSet;
    ReachResult res1 = reach.backwardSet(workingGraph, v);
    symbolicSteps = symbolicSteps + res1.symbolicSteps;
    backwardSet = res1.set;

    //Find the forwardset and stop quickly if the forwardset goes beyond the backwardset since the SCC is not a BSCC
    ReachResultBottom res2 = reach.forwardSetShortcut(workingGraph, v, backwardSet);
    symbolicSteps = symbolicSteps + res2.symbolicSteps;
    forwardSet = res2.set;
    bool isBscc = res2.isBscc;

    //Add scc to bscclist if it is a BSCC
    if(isBscc) {
      Bdd scc = forwardSet;
      bsccList.push_back(scc);
    }

    //Emulating a recursive call by pushing to the stack
    //Delete the entire backward set from recursive call
    Bdd recBdd = differenceBdd(nodeSet, backwardSet);
    if(recBdd != leaf_false()) {
      recCalls++;
      callStack.push(recBdd);
    }
  }
  std::cout << ";" << recCalls;
  return createSccResult(bsccList, symbolicSteps);  
}

template<class ReachType>
SccResult xieBeerelBottomInitState(const Graph &initGraph) {
  int symbolicSteps = 0;

  std::list<Bdd> bsccList = {};
  //Return if graph is empty
  if(initGraph.nodes == leaf_false()) {
    return createSccResult(bsccList, symbolicSteps);
  }

  //The type of reachability used - relationUnion or saturation
  ReachType reach;

  //Initialize the set of relations and graph
  const BddSet fullCube = initGraph.cube;
  const std::deque<Relation> relationDeque = initGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_true();

  const ReachResult allNodesResult = reach.forwardSet(workingGraph, initGraph.nodes); 
  const Bdd allNodes = allNodesResult.set;
  symbolicSteps += allNodesResult.symbolicSteps;
  workingGraph.nodes = allNodes;

  //callstack used to emulate recursive calls
  std::stack<Bdd> callStack;
  callStack.push(allNodes);

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet;
    Bdd backwardSet;

    workingGraph.nodes = nodeSet;
    ReachResult res1 = reach.backwardSet(workingGraph, v);
    symbolicSteps = symbolicSteps + res1.symbolicSteps;
    backwardSet = res1.set;

    //Find the forwardset and stop quickly if the forwardset goes beyond the backwardset since the SCC is not a BSCC
    ReachResultBottom res2 = reach.forwardSetShortcut(workingGraph, v, backwardSet);
    symbolicSteps = symbolicSteps + res2.symbolicSteps;
    forwardSet = res2.set;
    bool isBscc = res2.isBscc;

    //Add scc to bscclist if it is a BSCC
    if(isBscc) {
      Bdd scc = forwardSet;
      bsccList.push_back(scc);
    }

    //Emulating a recursive call by pushing to the stack
    //Delete the entire backward set from recursive call
    Bdd recBdd = differenceBdd(nodeSet, backwardSet);
    if(recBdd != leaf_false()) {
      callStack.push(recBdd);
    }
  }

  return createSccResult(bsccList, symbolicSteps);  
}

#endif // BSCC_H