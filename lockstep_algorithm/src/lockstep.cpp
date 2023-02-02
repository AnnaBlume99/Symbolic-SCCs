#include <iostream>
#include <list>
#include <deque>
#include <stack>
#include <vector>
#include <chrono>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "lockstep.h"
#include "bdd_utilities.h"

using sylvan::Bdd;
using sylvan::BddSet;

//Picks a single assignment in a given nodeSet. It takes the false path in the BDD as much as possible until finding a true leaf,
// and uses this path as assignment
Bdd pick(const Bdd &nodeSet, const BddSet &cube) {
	//Find path in BDD that evaluates to true, and evaluate the decisions into new node
  Bdd picked = pickAssignment(nodeSet, cube);
	return picked;
}

SccResult createSccResult(const std::list<Bdd> &sccs, const int symbolicSteps) {
  SccResult result = {};
  result.sccs = sccs;
  result.symbolicSteps = symbolicSteps;
  return result;
}

//SKELETON ####################################################################################
SccResult skeletonAlg(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  const Bdd allNodes = fullGraph.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  std::stack<std::pair<Bdd, std::pair<Bdd, Bdd>>> callStack;
  const Bdd startNode = pick(allNodes, fullCube);
  const Bdd skeleton = leaf_false();
  const std::pair<Bdd, Bdd> skelNodePair = {skeleton, startNode};
  std::pair<Bdd, std::pair<Bdd, Bdd>> pushPair = {allNodes, skelNodePair};
  callStack.push(pushPair);
  
  while(!callStack.empty()) {
    const std::pair<Bdd, std::pair<Bdd, Bdd>> nodeSetSkelStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetSkelStartNode);
    const std::pair<Bdd, Bdd> skelStartNode = std::get<1>(nodeSetSkelStartNode);
    const Bdd skeleton = std::get<0>(skelStartNode);
    const Bdd startNode = std::get<1>(skelStartNode);

    //Find skeleton
    Graph forwardGraph = {};
    forwardGraph.nodes = nodeSet;
    forwardGraph.cube = fullCube;
    forwardGraph.relations = relationDeque;

    SkeletonResult skelRes = skeletonForward(forwardGraph, startNode);
    const Bdd forwardSet = skelRes.forwardSet;
    const Bdd newSkeleton = skelRes.skeleton;
    const Bdd newStartNode = skelRes.node;
    const int symbolicStepsSkel = skelRes.symbolicSteps;
    symbolicSteps = symbolicSteps + symbolicStepsSkel;

    //find SCC
    Bdd scc = startNode;
    while(true) {
      Bdd relPrevScc = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        Bdd currentRelation = relationDeque[i].relationBdd;
        BddSet currentRelationCube = relationDeque[i].cube;

        Bdd relResultBack = intersectBdd(scc.RelPrev(currentRelation, currentRelationCube), nodeSet);
        symbolicSteps = symbolicSteps + 1;

        relPrevScc = unionBdd(relPrevScc, relResultBack);
      }

      Bdd toAdd = differenceBdd(intersectBdd(relPrevScc, forwardSet), scc);
      scc = unionBdd(scc, toAdd);
      if(toAdd == leaf_false()) {
        break;
      }
    }

    //Report the SCC
    sccList.push_back(scc);

    //Create "recursive" calls
    const Bdd recBdd1 = differenceBdd(nodeSet, forwardSet);
    if(recBdd1 != leaf_false()) {
      const Bdd recSkel1 = differenceBdd(skeleton, scc);

      Bdd sccSkel = intersectBdd(scc, skeleton);
      Bdd relPrevSccSkel = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        Bdd currentRelation = relationDeque[i].relationBdd;
        BddSet currentRelationCube = relationDeque[i].cube;

        Bdd relResultBack = intersectBdd(sccSkel.RelPrev(currentRelation, currentRelationCube), nodeSet);
        symbolicSteps = symbolicSteps + 1;

        relPrevSccSkel = unionBdd(relPrevSccSkel, relResultBack);
      }

      Bdd recNode1 = leaf_false();
      if(recSkel1 != leaf_false()) {
        recNode1 = intersectBdd(relPrevSccSkel, differenceBdd(skeleton, scc));
      } else {
        recNode1 = pick(recBdd1, fullCube);
      }
      
      const std::pair<Bdd, Bdd> recSkelNode1 = {recSkel1, recNode1};
      const std::pair<Bdd, std::pair<Bdd, Bdd>> recSet1 = {recBdd1, recSkelNode1};
      callStack.push(recSet1);
    }

    const Bdd recBdd2 = differenceBdd(forwardSet, scc);
    if(recBdd2 != leaf_false()) {
      const Bdd recSkel2 = differenceBdd(newSkeleton, scc);

      Bdd recNode2 = leaf_false();
      if(recSkel2 != leaf_false()) {
        recNode2 = differenceBdd(newStartNode, scc);
      } else {
        recNode2 = pick(recBdd2, fullCube);
      }

      const std::pair<Bdd, Bdd> recSkelNode2 = {recSkel2, recNode2};
      const std::pair<Bdd, std::pair<Bdd, Bdd>> recSet2 = {recBdd2, recSkelNode2};
      callStack.push(recSet2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

// CHAIN Algorithm ####################################################################################
SccResult chainAlg(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  const Bdd allNodes = fullGraph.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  std::stack<std::pair<Bdd, Bdd>> callStack;
  const Bdd startNode = pick(allNodes, fullCube);
  const std::pair<Bdd, Bdd> pushPair = {allNodes, startNode};
  callStack.push(pushPair);
  
  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //Compute the forward transitive closure and keep the last layer of the computation
    Graph forwardGraph = {};
    forwardGraph.nodes = nodeSet;
    forwardGraph.cube = fullCube;
    forwardGraph.relations = relationDeque;
    const ChainResult transForward = reachabilityForwardRelationUnionLastLayer(forwardGraph, startNode);
    const Bdd forwardSet = transForward.forwardSet;
    const Bdd lastForwardLayer = transForward.lastLayer;
    const int symbolicStepsForward = transForward.symbolicSteps;
    symbolicSteps = symbolicSteps + symbolicStepsForward;

    RelationUnion rel;

    //Compute the backward transitive closure on the result of forward (result is the SCC)
    Graph backwardGraph = {};
    backwardGraph.nodes = forwardSet;
    backwardGraph.cube = fullCube;
    backwardGraph.relations = relationDeque;
    const ReachResult transBackward = rel.backwardSet(backwardGraph, startNode);
    const Bdd scc = transBackward.set;
    symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

    //Report the SCC
    sccList.push_back(scc);

    //Create "recursive" calls
    const Bdd recBdd1 = differenceBdd(forwardSet, scc);
    if(recBdd1 != leaf_false()) {
      const Bdd recNodeSet1 = differenceBdd(lastForwardLayer, scc);
      Bdd recNode1;
      if(recNodeSet1 != leaf_false()) {
        recNode1 = pick(recNodeSet1, fullCube);
      } else {
        recNode1 = pick(recBdd1, fullCube);
      }
      const std::pair<Bdd, Bdd> recPair1 = {recBdd1, recNode1};
      callStack.push(recPair1);
    }

    const Bdd recBdd2 = differenceBdd(nodeSet, forwardSet);
    if(recBdd2 != leaf_false()) {
      Bdd relPrevScc = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        Bdd currentRelation = relationDeque[i].relationBdd;
        BddSet currentRelationCube = relationDeque[i].cube;

        Bdd relResultBack = scc.RelPrev(currentRelation, currentRelationCube);
        symbolicSteps = symbolicSteps + 1;

        relPrevScc = unionBdd(relPrevScc, relResultBack);
      }
      Bdd recNodeSet2 = intersectBdd(relPrevScc, differenceBdd(nodeSet, forwardSet));
      Bdd recNode2;
      if(recNodeSet2 != leaf_false()) {
        recNode2 = pick(recNodeSet2, fullCube);
      } else {
        recNode2 = pick(recBdd2, fullCube);
      }
      std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

// LOCKSTEP ########################################################################################
SccResult lockstepSaturation(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  //Things pulled out from while-loop
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet = v;
    //printBdd(forwardSet);
    Bdd backwardSet = v;

    int relFrontI = 0;
    Relation r = relationDeque[relFrontI];
    Bdd relFront = r.relationBdd;
    //printBdd(relFront);
    BddSet relFrontCube = relationDeque[relFrontI].cube;

    int relBackI = 0;
    Bdd relBack = relationDeque[relBackI].relationBdd;
    BddSet relBackCube = relationDeque[relBackI].cube;

    //Expand both forward and backward sets until one converges
    while(relFrontI < relationDeque.size() && relBackI < relationDeque.size()) {
      //Find images
      Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
      Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
      symbolicSteps = symbolicSteps + 2;

      //Update relations
      if(relResultFront == leaf_false()) {
        relFrontI++;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      } else {
        relFrontI = 0;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      }
      if(relResultBack == leaf_false()) {
        relBackI++;
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      } else {
        relBackI = 0;
        relBack = relationDeque[0].relationBdd;
        relBackCube = relationDeque[0].cube;
      }

      //Add to the forward and backward sets
      forwardSet = unionBdd(forwardSet, relResultFront);
      backwardSet = unionBdd(backwardSet, relResultBack);
    }

    //Save the set that has converged and the one that didn't
    bool frontConverged = relFrontI == relationDeque.size();
    Bdd converged = frontConverged ? forwardSet : backwardSet;
    Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

    //Throw away the elements from the nonConverged set that won't be part of the SCC
    nonConverged = intersectBdd(converged, nonConverged);
    if(frontConverged) {
      backwardSet = nonConverged;
    } else {
      forwardSet = nonConverged;
    }

    while(relFrontI < relationDeque.size()) {
      Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), backwardSet), forwardSet);
      symbolicSteps++;
      if(relResultFront == leaf_false()) {
        relFrontI++;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      } else {
        relFrontI = 0;
        relFront = relationDeque[0].relationBdd;
        relFrontCube = relationDeque[0].cube;
        forwardSet = unionBdd(forwardSet, relResultFront);
      }
    }

    while(relBackI < relationDeque.size()) {
      Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), forwardSet), backwardSet);
      symbolicSteps++;
      if(relResultBack == leaf_false()) {
        relBackI++;
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      } else {
        relBackI = 0;
        relBack = relationDeque[0].relationBdd;
        relBackCube = relationDeque[0].cube;
        backwardSet = unionBdd(backwardSet, relResultBack);
      }
    }

    //Create SCC
    Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

SccResult lockstepRelationUnion(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  //Things pulled out from while-loop
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet = v;
    Bdd backwardSet = v;

    //This is the "ring" that we find the next ring from
    Bdd forwardFront = v;
    Bdd backwardFront = v;

    //This is the accumulator for the next ring
    Bdd forwardAcc = leaf_false();
    Bdd backwardAcc = leaf_false();

    Bdd relResultFront;
    Bdd relResultBack;

    Bdd currentRelation;
    BddSet currentRelationCube;

    //Expand both forward and backward sets until one converges
    bool somethingChangedFront = true;
    bool somethingChangedBack = true;

    while(somethingChangedFront && somethingChangedBack) {
      somethingChangedFront = false;
      somethingChangedBack = false;

      for(int i = 0 ; i < relationDeque.size(); i++) {
        currentRelation = relationDeque[i].relationBdd;
        currentRelationCube = relationDeque[i].cube;

        //Finds part of the next ring with the active relation
        Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
        Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
        symbolicSteps = symbolicSteps + 2;

        //We accumulate the entire ring by adding the partial rings from all relations
        forwardAcc = unionBdd(forwardAcc, relResultFront);
        backwardAcc = unionBdd(backwardAcc, relResultBack);
      }

      if(forwardAcc != leaf_false()) {
        somethingChangedFront = true;
      }
      if(backwardAcc != leaf_false()) {
        somethingChangedBack = true;
      }

      //Add everything to forward and backward sets
      forwardSet = unionBdd(forwardSet, forwardAcc);
      backwardSet = unionBdd(backwardSet, backwardAcc);

      //We need to subtract the previous ring from the accumulators to only get the new rings, which are then stored in the new fronts
      forwardFront = differenceBdd(forwardAcc, forwardFront);
      forwardAcc = leaf_false();
      backwardFront = differenceBdd(backwardAcc, backwardFront);
      backwardAcc = leaf_false();
    }

    //Save the set that has converged
    bool frontConverged = !somethingChangedFront;
    Bdd converged = frontConverged ? forwardSet : backwardSet;
    Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

    //Throw away the elements from the nonConverged set that won't be part of the SCC
    nonConverged = intersectBdd(converged, nonConverged);
    if(frontConverged) {
      backwardSet = nonConverged;
    } else {
      forwardSet = nonConverged;
    }

    while(somethingChangedFront) {
      somethingChangedFront = false;
        for(int i = 0 ; i < relationDeque.size(); i++) {
          currentRelation = relationDeque[i].relationBdd;
          currentRelationCube = relationDeque[i].cube;

          //Finds part of the next ring with the active relation
          Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), backwardSet), forwardSet);
          symbolicSteps++;
          forwardAcc = unionBdd(forwardAcc, relResultFront);
        }
        if(forwardAcc != leaf_false()) {
          somethingChangedFront = true;
        }
        forwardSet = unionBdd(forwardSet, forwardAcc);

        //Find new ring and reset accumulator
        forwardFront = differenceBdd(forwardAcc, forwardFront);
        forwardAcc = leaf_false();
    }

    while(somethingChangedBack) {
      somethingChangedBack = false;
        for(int i = 0 ; i < relationDeque.size(); i++) {
          currentRelation = relationDeque[i].relationBdd;
          currentRelationCube = relationDeque[i].cube;

          //Finds part of the next ring with the active relation
          Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), forwardSet), backwardSet);
          symbolicSteps++;
          backwardAcc = unionBdd(backwardAcc, relResultBack);
        }
        if(backwardAcc != leaf_false()) {
          somethingChangedBack = true;
        }
        backwardSet = unionBdd(backwardSet, backwardAcc);

        //Find new ring and reset accumulator
        backwardFront = differenceBdd(backwardAcc, backwardFront);
        backwardAcc = leaf_false();
    }

    //Create SCC
    Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to SCC list
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

// XIE-BEEREL ######################################################################################
SccResult xieBeerelSaturation(const Graph &fullGraph) {
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

  Saturation sat;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet = v;
    Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;
    ReachResult res1 = sat.forwardSet(workingGraph, forwardSet);
    forwardSet = res1.set;
    symbolicSteps = symbolicSteps + res1.symbolicSteps;

    workingGraph.nodes = forwardSet;

    ReachResult res2 = sat.backwardSet(workingGraph, backwardSet);
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

SccResult xieBeerelRelationUnion(const Graph &fullGraph) {
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

  RelationUnion rel;

  while(!callStack.empty()) {
    const Bdd nodeSet = callStack.top();
    callStack.pop();

    Bdd v = pick(nodeSet, fullCube);
    Bdd forwardSet = v;
    Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    ReachResult res1 = rel.forwardSet(workingGraph, forwardSet);
    forwardSet = res1.set;
    symbolicSteps = symbolicSteps + res1.symbolicSteps;

    workingGraph.nodes = forwardSet;

    ReachResult res2 = rel.backwardSet(workingGraph, backwardSet);
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

// REACHABILITY ####################################################################################
ChainResult reachabilityForwardRelationUnionLastLayer(const Graph &graph, const Bdd &nodes) {
  BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  Bdd forwardSet = nodes;
  Bdd nodeSet = graph.nodes;

  Bdd forwardFront = nodes;
  Bdd forwardAcc = leaf_false();
  Bdd relResultFront;

  Bdd currentRelation;
  BddSet currentRelationCube;

  int symbolicSteps = 0;

  Bdd lastLayer;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
      symbolicSteps++;
      forwardAcc = unionBdd(forwardAcc, relResultFront);
    }

    forwardFront = differenceBdd(forwardAcc, forwardSet);
    forwardSet = unionBdd(forwardSet, forwardFront);

    if(forwardFront != leaf_false()) {
      somethingChanged = true;
      lastLayer = forwardFront;
    }

    forwardAcc = leaf_false();
  }

  ChainResult result = {};
  result.forwardSet = forwardSet;
  result.lastLayer = lastLayer;
  result.symbolicSteps = symbolicSteps;
  return result;
}

SkeletonResult skeletonForward(const Graph &graph, const Bdd &nodes) {
  BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;
  Bdd nodeSet = graph.nodes;

  std::stack<Bdd> skelStack;

  Bdd forwardSet = nodes;
  skelStack.push(forwardSet);

  Bdd forwardFront = nodes;
  Bdd forwardAcc = leaf_false();
  Bdd relResultFront;

  Bdd currentRelation;
  BddSet currentRelationCube;

  int symbolicSteps = 0;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      relResultFront = intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet);
      symbolicSteps++;
      forwardAcc = unionBdd(forwardAcc, relResultFront);
    }

    forwardFront = differenceBdd(forwardAcc, forwardSet);
    forwardSet = unionBdd(forwardSet, forwardFront);

    if(forwardFront != leaf_false()) {
      somethingChanged = true;
      skelStack.push(forwardFront);
    }

    forwardAcc = leaf_false();
  }

  Bdd layer = skelStack.top();
  skelStack.pop();
  Bdd newStartNode = pick(layer, cube);
  Bdd newSkeleton = newStartNode;
  while(!skelStack.empty()) {
    layer = skelStack.top();
    skelStack.pop();

    Bdd relPrevSkel = leaf_false();
    for(int i = 0 ; i < relationDeque.size(); i++) {
      Bdd currentRelation = relationDeque[i].relationBdd;
      BddSet currentRelationCube = relationDeque[i].cube;

      Bdd relResultBack = intersectBdd(newSkeleton.RelPrev(currentRelation, currentRelationCube), nodeSet);
      symbolicSteps = symbolicSteps + 1;

      relPrevSkel = unionBdd(relPrevSkel, relResultBack);
    }

    Bdd prevIntersectLayer = intersectBdd(relPrevSkel, layer);
    Bdd pickNodeFromPrev = pick(prevIntersectLayer, cube);
    newSkeleton = unionBdd(newSkeleton, pickNodeFromPrev);
  }

  SkeletonResult result = {};
  result.forwardSet = forwardSet;
  result.skeleton = newSkeleton;
  result.node = newStartNode;
  result.symbolicSteps = symbolicSteps;
  return result;
}
