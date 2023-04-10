#include <iostream>
#include <list>
#include <deque>
#include <stack>
#include <vector>
#include <chrono>
#include <set>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "scc.h"
#include "bdd_utilities.h"
#include "print.h"
#include "bscc.h"

using sylvan::Bdd;
using sylvan::BddSet;


std::pair<SccResult, Graph> deadlockRemoval(const Graph &fullGraph) {
  RelationUnion rel;
  int symbolicSteps = 0;
  Bdd nodes = fullGraph.nodes;
  std::list<Bdd> sccList = {};
  const BddSet fullCube = fullGraph.cube;

  ReachResult postAll = rel.forwardStep2(fullGraph, nodes);
  symbolicSteps = symbolicSteps + postAll.symbolicSteps;
  Bdd post = postAll.set;

  ReachResult prePostAll = rel.backwardStep2(fullGraph, post);
  symbolicSteps = symbolicSteps + prePostAll.symbolicSteps;
  Bdd hasSuccessor = prePostAll.set;

  //These are all 1 node BSCCs
  Bdd doesNotHaveSuccessor = differenceBdd(nodes, hasSuccessor);

  //We can remove these BSCCs and their basins safely (when we have outputted them)
  ReachResult toRemove = rel.backwardSet(fullGraph, doesNotHaveSuccessor);
  symbolicSteps = symbolicSteps + toRemove.symbolicSteps;

  //Report BSCCs
  while(doesNotHaveSuccessor != leaf_false()) {
    Bdd bscc = pick(doesNotHaveSuccessor, fullCube);
    sccList.push_back(bscc);
    doesNotHaveSuccessor = differenceBdd(doesNotHaveSuccessor, bscc);
  }

  //Output result
  Graph graphRes = {};
  graphRes.nodes = differenceBdd(nodes, toRemove.set);
  graphRes.relations = fullGraph.relations;
  graphRes.cube = fullGraph.cube;
  SccResult sccRes = createSccResult(sccList, symbolicSteps);

  std::pair<SccResult, Graph> pairRes = {sccRes, graphRes};
  return pairRes;
}

ReachResult sourceRemoval(const Graph &fullGraph) {
  RelationUnion rel;
  int symbolicSteps = 0;
  Bdd nodes = fullGraph.nodes;

  ReachResult preAll = rel.backwardStep(fullGraph, nodes);
  symbolicSteps = symbolicSteps + preAll.symbolicSteps;
  Bdd pre = preAll.set;

  ReachResult postPreAll = rel.forwardStep(fullGraph, pre);
  symbolicSteps = symbolicSteps + postPreAll.symbolicSteps;
  Bdd hasPredecessor = postPreAll.set;

  Bdd doesNotHavePredecessor = differenceBdd(nodes, hasPredecessor);

  ReachResult res = {};
  res.set = differenceBdd(nodes, doesNotHavePredecessor);
  res.symbolicSteps = symbolicSteps;
  return res;
}
