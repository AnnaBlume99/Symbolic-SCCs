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

SccResult chainAlgBottomBasic(const Graph &fullGraph);
SccResult chainAlgBottomAdvanced(const Graph &fullGraph);


template<class ReachType>
SccResult xieBeerelBottom(const Graph &fullGraph) {
  int symbolicSteps = 0;

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
    backwardSet = res1.set;
    symbolicSteps = symbolicSteps + res1.symbolicSteps;

    //Find the forwardset and stop quickly if the forwardset goes beyond the backwardset since the SCC is not a BSCC
    ReachResultBottom res2 = reach.forwardSetShortcut(workingGraph, v, backwardSet);
    forwardSet = res2.set;
    symbolicSteps = symbolicSteps + res2.symbolicSteps;
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