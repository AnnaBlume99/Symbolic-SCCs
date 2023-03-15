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

using sylvan::Bdd;
using sylvan::BddSet;

SccResult chainAlgBottomAdvanced(const Graph &fullGraph);
SccResult chainAlgBottomSpecialFWD(const Graph &fullGraph);

SccResult chainAlgBottomSingleRecCall(const Graph &fullGraph);
SccResult chainAlgBottomSingleRecSpecialFWD(const Graph &fullGraph);

SccResult chainAlgBottomSingleRecForwardLoop(const Graph &fullGraph);
SccResult chainAlgBottomForwardLoop(const Graph &fullGraph);

template<class ReachType>
SccResult xieBeerelBottom(const Graph &fullGraph) {
  int symbolicSteps = 0;
  long long nodeCount = 0;
  int recCalls = 0;

  //callstack used to emulate recursive calls
  std::stack<Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<Bdd> bsccList = {};
  //Return if graph is empty
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(bsccList, symbolicSteps);
  }

  //Initialize the set of relations and graph
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

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
    nodeCount += res1.set.SatCount(fullCube);

    //Find the forwardset and stop quickly if the forwardset goes beyond the backwardset since the SCC is not a BSCC
    ReachResultBottom res2 = reach.forwardSetShortcut(workingGraph, v, backwardSet);
    symbolicSteps = symbolicSteps + res2.symbolicSteps;
    forwardSet = res2.set;
    bool isBscc = res2.isBscc;
    nodeCount += res2.set.SatCount(fullCube);

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
  std::cout << ";" << recCalls << ";" << nodeCount;
  return createSccResult(bsccList, symbolicSteps);  
}

#endif // BSCC_H