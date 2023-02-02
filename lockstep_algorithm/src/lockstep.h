#ifndef LOCKSTEP_H
#define LOCKSTEP_H

#include <deque>
#include<list>
#include<stack>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "petriTranslation.h"
#include "reachability.h"
#include "bdd_utilities.h"

using sylvan::Bdd;
using sylvan::BddSet;

struct SccResult {
  std::list<sylvan::Bdd> sccs;
  int symbolicSteps;
};

/*
This contains:
- Iterative versions of SCC-finding algorithms lockstep and Xie Beerel, both with and without Saturation
- Functions for computing forward and backward sets
- Pick function
*/

//Pick a single node from a nodeSet
sylvan::Bdd pick(const sylvan::Bdd &nodeSet, const sylvan::BddSet &cube);
SccResult createSccResult(const std::list<Bdd> &sccs, const int symbolicSteps);

//Skeleton algorithm
SccResult skeletonAlg(const Graph &fullGraph);

//Chain algorithm (new skeleton algorithm)
SccResult chainAlg(const Graph &fullGraph);

//Lockstep
SccResult lockstepSaturation(const Graph &fullGraph);
SccResult lockstepRelationUnion(const Graph &fullGraph);

//Xie-Beerel
template<class ReachType>
SccResult xieBeerel(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  ReachType reach;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet = v;
    Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;
    ReachResult res1 = reach.forwardSet(workingGraph, forwardSet);
    forwardSet = res1.set;
    symbolicSteps = symbolicSteps + res1.symbolicSteps;

    workingGraph.nodes = forwardSet;

    ReachResult res2 = reach.backwardSet(workingGraph, backwardSet);
    backwardSet = res2.set;
    symbolicSteps = symbolicSteps + res2.symbolicSteps;

    //Create SCC
    Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    Bdd recBdd1 = differenceBdd(forwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    Bdd recBdd2 = differenceBdd(nodeSet, forwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  return createSccResult(sccList, symbolicSteps);
}

#endif  //LOCKSTEP_H