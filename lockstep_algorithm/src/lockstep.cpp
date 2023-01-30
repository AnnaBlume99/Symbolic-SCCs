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

//Picks a single assignment in a given nodeSet. It takes the false path in the BDD as much as possible until finding a true leaf,
// and uses this path as assignment
sylvan::Bdd pick(const sylvan::Bdd &nodeSet, const sylvan::BddSet &cube) {
	//Find path in BDD that evaluates to true, and evaluate the decisions into new node
  sylvan::Bdd picked = pickAssignment(nodeSet, cube);
	return picked;
}

// OLD SKELETON ####################################################################################
std::pair<std::list<sylvan::Bdd>, int> oldSkeleton(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::Bdd allNodes = fullGraph.nodes;
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  std::stack<std::pair<sylvan::Bdd, std::pair<sylvan::Bdd, sylvan::Bdd>>> callStack;
  const sylvan::Bdd startNode = pick(allNodes, fullCube);
  const sylvan::Bdd skeleton = leaf_false();
  const std::pair<sylvan::Bdd, sylvan::Bdd> skelNodePair = {skeleton, startNode};
  std::pair<sylvan::Bdd, std::pair<sylvan::Bdd, sylvan::Bdd>> pushPair = {allNodes, skelNodePair};
  callStack.push(pushPair);
  
  while(!callStack.empty()) {
    const std::pair<sylvan::Bdd, std::pair<sylvan::Bdd, sylvan::Bdd>> nodeSetSkelStartNode = callStack.top();
    callStack.pop();
    const sylvan::Bdd nodeSet = std::get<0>(nodeSetSkelStartNode);
    const std::pair<sylvan::Bdd, sylvan::Bdd> skelStartNode = std::get<1>(nodeSetSkelStartNode);
    const sylvan::Bdd skeleton = std::get<0>(skelStartNode);
    const sylvan::Bdd startNode = std::get<1>(skelStartNode);

    //Find skeleton
    Graph forwardGraph = {};
    forwardGraph.nodes = nodeSet;
    forwardGraph.cube = fullCube;
    forwardGraph.relations = relationDeque;

    std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, std::pair<sylvan::Bdd, int>> skelRes = skeletonForward(forwardGraph, startNode);
    const std::pair<sylvan::Bdd, sylvan::Bdd> forwardSkel = std::get<0>(skelRes);
    const sylvan::Bdd forwardSet = std::get<0>(forwardSkel);
    const sylvan::Bdd newSkeleton = std::get<1>(forwardSkel);
    const std::pair<sylvan::Bdd, int> nodeSteps = std::get<1>(skelRes);
    const sylvan::Bdd newStartNode = std::get<0>(nodeSteps);
    const int symbolicStepsSkel = std::get<1>(nodeSteps);
    symbolicSteps = symbolicSteps + symbolicStepsSkel;

    //find SCC
    sylvan::Bdd scc = startNode;
    while(true) {
      sylvan::Bdd relPrevScc = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        sylvan::Bdd currentRelation = relationDeque[i].relationBdd;
        sylvan::BddSet currentRelationCube = relationDeque[i].cube;

        sylvan::Bdd relResultBack = intersectBdd(scc.RelPrev(currentRelation, currentRelationCube), nodeSet);
        symbolicSteps = symbolicSteps + 1;

        relPrevScc = unionBdd(relPrevScc, relResultBack);
      }

      sylvan::Bdd toAdd = differenceBdd(intersectBdd(relPrevScc, forwardSet), scc);
      scc = unionBdd(scc, toAdd);
      if(toAdd == leaf_false()) {
        break;
      }
    }

    //Report the SCC
    sccList.push_back(scc);

    //Create "recursive" calls
    const sylvan::Bdd recBdd1 = differenceBdd(nodeSet, forwardSet);
    if(recBdd1 != leaf_false()) {
      const sylvan::Bdd recSkel1 = differenceBdd(skeleton, scc);

      sylvan::Bdd sccSkel = intersectBdd(scc, skeleton);
      sylvan::Bdd relPrevSccSkel = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        sylvan::Bdd currentRelation = relationDeque[i].relationBdd;
        sylvan::BddSet currentRelationCube = relationDeque[i].cube;

        sylvan::Bdd relResultBack = intersectBdd(sccSkel.RelPrev(currentRelation, currentRelationCube), nodeSet);
        symbolicSteps = symbolicSteps + 1;

        relPrevSccSkel = unionBdd(relPrevSccSkel, relResultBack);
      }

      sylvan::Bdd recNode1 = leaf_false();
      if(recSkel1 != leaf_false()) {
        recNode1 = intersectBdd(relPrevSccSkel, differenceBdd(skeleton, scc));
      } else {
        recNode1 = pick(recBdd1, fullCube);
      }
      
      const std::pair<sylvan::Bdd, sylvan::Bdd> recSkelNode1 = {recSkel1, recNode1};
      const std::pair<sylvan::Bdd, std::pair<sylvan::Bdd, sylvan::Bdd>> recSet1 = {recBdd1, recSkelNode1};
      callStack.push(recSet1);
    }

    const sylvan::Bdd recBdd2 = differenceBdd(forwardSet, scc);
    if(recBdd2 != leaf_false()) {
      const sylvan::Bdd recSkel2 = differenceBdd(newSkeleton, scc);

      sylvan::Bdd recNode2 = leaf_false();
      if(recSkel2 != leaf_false()) {
        recNode2 = differenceBdd(newStartNode, scc);
      } else {
        recNode2 = pick(recBdd2, fullCube);
      }

      const std::pair<sylvan::Bdd, sylvan::Bdd> recSkelNode2 = {recSkel2, recNode2};
      const std::pair<sylvan::Bdd, std::pair<sylvan::Bdd, sylvan::Bdd>> recSet2 = {recBdd2, recSkelNode2};
      callStack.push(recSet2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

// NEW SKELETON ####################################################################################
std::pair<std::list<sylvan::Bdd>, int> newSkeleton(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::Bdd allNodes = fullGraph.nodes;
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  std::stack<std::pair<sylvan::Bdd, sylvan::Bdd>> callStack;
  const sylvan::Bdd startNode = pick(allNodes, fullCube);
  const std::pair<sylvan::Bdd, sylvan::Bdd> pushPair = {allNodes, startNode};
  callStack.push(pushPair);
  
  while(!callStack.empty()) {
    const std::pair<sylvan::Bdd, sylvan::Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const sylvan::Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const sylvan::Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //Compute the forward transitive closure and keep the last layer of the computation
    Graph forwardGraph = {};
    forwardGraph.nodes = nodeSet;
    forwardGraph.cube = fullCube;
    forwardGraph.relations = relationDeque;
    const std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, int> transForward = reachabilityForwardRelationUnionLastLayer(forwardGraph, startNode);
    const std::pair<sylvan::Bdd, sylvan::Bdd> forwardSetAndLastLayer = std::get<0>(transForward);
    const sylvan::Bdd forwardSet = std::get<0>(forwardSetAndLastLayer);
    const sylvan::Bdd lastForwardLayer = std::get<1>(forwardSetAndLastLayer);
    const int symbolicStepsForward = std::get<1>(transForward);
    symbolicSteps = symbolicSteps + symbolicStepsForward;

    //Compute the backward transitive closure on the result of forward (result is the SCC)
    Graph backwardGraph = {};
    backwardGraph.nodes = forwardSet;
    backwardGraph.cube = fullCube;
    backwardGraph.relations = relationDeque;
    const std::pair<sylvan::Bdd, int> transBackward = reachabilityBackwardRelationUnion(backwardGraph, startNode);
    const sylvan::Bdd scc = std::get<0>(transBackward);
    const int symbolicStepsBackward = std::get<1>(transBackward);
    symbolicSteps = symbolicSteps + symbolicStepsBackward;

    //Report the SCC
    sccList.push_back(scc);

    //Create "recursive" calls
    const sylvan::Bdd recBdd1 = differenceBdd(forwardSet, scc);
    if(recBdd1 != leaf_false()) {
      const sylvan::Bdd recNodeSet1 = differenceBdd(lastForwardLayer, scc);
      sylvan::Bdd recNode1;
      if(recNodeSet1 != leaf_false()) {
        recNode1 = pick(recNodeSet1, fullCube);
      } else {
        recNode1 = pick(recBdd1, fullCube);
      }
      const std::pair<sylvan::Bdd, sylvan::Bdd> recPair1 = {recBdd1, recNode1};
      callStack.push(recPair1);
    }

    const sylvan::Bdd recBdd2 = differenceBdd(nodeSet, forwardSet);
    if(recBdd2 != leaf_false()) {
      sylvan::Bdd relPrevScc = leaf_false();
      for(int i = 0 ; i < relationDeque.size(); i++) {
        sylvan::Bdd currentRelation = relationDeque[i].relationBdd;
        sylvan::BddSet currentRelationCube = relationDeque[i].cube;

        sylvan::Bdd relResultBack = scc.RelPrev(currentRelation, currentRelationCube);
        symbolicSteps = symbolicSteps + 1;

        relPrevScc = unionBdd(relPrevScc, relResultBack);
      }
      sylvan::Bdd recNodeSet2 = intersectBdd(relPrevScc, differenceBdd(nodeSet, forwardSet));
      sylvan::Bdd recNode2;
      if(recNodeSet2 != leaf_false()) {
        recNode2 = pick(recNodeSet2, fullCube);
      } else {
        recNode2 = pick(recBdd2, fullCube);
      }
      std::pair<sylvan::Bdd, sylvan::Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

// LOCKSTEP ########################################################################################
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturation(const Graph &fullGraph) {
  /*auto start = std::chrono::high_resolution_clock::now();
  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);*/

  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  //Things pulled out from while-loop
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    //printBdd(forwardSet);
    sylvan::Bdd backwardSet = v;

    int relFrontI = 0;
    Relation r = relationDeque[relFrontI];
    sylvan::Bdd relFront = r.relationBdd;
    //printBdd(relFront);
    sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

    int relBackI = 0;
    sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
    sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

    //Expand both forward and backward sets until one converges
    while(relFrontI < relationDeque.size() && relBackI < relationDeque.size()) {
      //Find images
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
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
    sylvan::Bdd converged = frontConverged ? forwardSet : backwardSet;
    sylvan::Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

    //Throw away the elements from the nonConverged set that won't be part of the SCC
    nonConverged = intersectBdd(converged, nonConverged);
    if(frontConverged) {
      backwardSet = nonConverged;
    } else {
      forwardSet = nonConverged;
    }

    while(relFrontI < relationDeque.size()) {
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), backwardSet), forwardSet);
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
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), forwardSet), backwardSet);
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
    sylvan::Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> lockstepRelationUnion(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  //Things pulled out from while-loop
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    //This is the "ring" that we find the next ring from
    sylvan::Bdd forwardFront = v;
    sylvan::Bdd backwardFront = v;

    //This is the accumulator for the next ring
    sylvan::Bdd forwardAcc = leaf_false();
    sylvan::Bdd backwardAcc = leaf_false();

    sylvan::Bdd relResultFront;
    sylvan::Bdd relResultBack;

    sylvan::Bdd currentRelation;
    sylvan::BddSet currentRelationCube;

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
        sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
        sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
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
    sylvan::Bdd converged = frontConverged ? forwardSet : backwardSet;
    sylvan::Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

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
          sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), backwardSet), forwardSet);
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
          sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), forwardSet), backwardSet);
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
    sylvan::Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to SCC list
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

// XIE-BEEREL ######################################################################################
std::pair<std::list<sylvan::Bdd>, int> xieBeerelForwardSaturation(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;
    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardSaturation(workingGraph, forwardSet);
    forwardSet = res1.first;
    symbolicSteps = symbolicSteps + res1.second;

    workingGraph.nodes = forwardSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardSaturation(workingGraph, backwardSet);
    backwardSet = res2.first;
    symbolicSteps = symbolicSteps + res2.second;

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(forwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, forwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturation(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardSaturation(workingGraph, backwardSet);
    backwardSet = res2.first;
    symbolicSteps = symbolicSteps + res2.second;

    workingGraph.nodes = backwardSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardSaturation(workingGraph, forwardSet);
    forwardSet = res1.first;
    symbolicSteps = symbolicSteps + res1.second;

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(backwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, backwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> xieBeerelForwardRelationUnion(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();


  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardRelationUnion(workingGraph, forwardSet);
    forwardSet = res1.first;
    symbolicSteps = symbolicSteps + res1.second;

    workingGraph.nodes = forwardSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardRelationUnion(workingGraph, backwardSet);
    backwardSet = res2.first;
    symbolicSteps = symbolicSteps + res2.second;

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(forwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, forwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> xieBeerelRelationUnion(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();


  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardRelationUnion(workingGraph, backwardSet);
    backwardSet = res2.first;
    symbolicSteps = symbolicSteps + res2.second;

    workingGraph.nodes = backwardSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardRelationUnion(workingGraph, forwardSet);
    forwardSet = res1.first;
    symbolicSteps = symbolicSteps + res1.second;

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(backwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, backwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

// REACHABILITY ####################################################################################
std::pair<sylvan::Bdd, int> reachabilityForwardSaturation(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relFrontI = 0;
  sylvan::Bdd relFront = relationDeque[relFrontI].relationBdd;
  sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

  int symbolicSteps = 0;

  while(relFrontI < relationDeque.size()) {
    sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
    symbolicSteps++;

    if(relResultFront == leaf_false()) {
      relFrontI++;
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    } else {
      relFrontI = 0;
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    }

	  //Add to the forward set
    forwardSet = unionBdd(forwardSet, relResultFront);
  }

  std::pair<sylvan::Bdd, int> result = {forwardSet, symbolicSteps};
  return result;
}

std::pair<sylvan::Bdd, int> reachabilityBackwardSaturation(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd backwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relBackI = 0;
  sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
  sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

  int symbolicSteps = 0;

  while(relBackI < relationDeque.size()) {
  //Find images
    sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
    symbolicSteps++;

    if(relResultBack == leaf_false()) {
      relBackI++;
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    } else {
      relBackI = 0;
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    }

    //Add to the forward and backward sets
    backwardSet = unionBdd(backwardSet, relResultBack);
  }

  std::pair<sylvan::Bdd, int> result = {backwardSet, symbolicSteps};
  return result;
}

std::pair<sylvan::Bdd, int> reachabilityForwardRelationUnion(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  sylvan::Bdd forwardFront = nodes;
  sylvan::Bdd forwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

  int symbolicSteps = 0;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
      symbolicSteps++;
      forwardAcc = unionBdd(forwardAcc, relResultFront);
    }

    if(forwardAcc != leaf_false()) {
      somethingChanged = true;
    }
    forwardSet = unionBdd(forwardSet, forwardAcc);

    forwardFront = differenceBdd(forwardAcc, forwardFront);
    forwardAcc = leaf_false();
  }
  std::pair<sylvan::Bdd, int> result = {forwardSet, symbolicSteps};
  return result;
}

std::pair<sylvan::Bdd, int> reachabilityBackwardRelationUnion(const Graph &graph, sylvan::Bdd nodes) {
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd backwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  sylvan::Bdd backwardFront = nodes;
  sylvan::Bdd backwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

  int symbolicSteps = 0;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
      symbolicSteps++;
      backwardAcc = unionBdd(backwardAcc, relResultFront);
    }

    if(backwardAcc != leaf_false()) {
      somethingChanged = true;
    }
    backwardSet = unionBdd(backwardSet, backwardAcc);

    backwardFront = differenceBdd(backwardAcc, backwardFront);
    backwardAcc = leaf_false();
  }

  std::pair<sylvan::Bdd, int> result = {backwardSet, symbolicSteps};
  return result;
}

std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, int> reachabilityForwardRelationUnionLastLayer(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  sylvan::Bdd forwardFront = nodes;
  sylvan::Bdd forwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

  int symbolicSteps = 0;

  sylvan::Bdd lastLayer;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
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
  std::pair<sylvan::Bdd, sylvan::Bdd> setAndLastLayer = {forwardSet, lastLayer};
  std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, int> result = {setAndLastLayer, symbolicSteps};
  return result;
}

std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, std::pair<sylvan::Bdd, int>> skeletonForward(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;
  sylvan::Bdd nodeSet = graph.nodes;

  std::stack<sylvan::Bdd> skelStack;

  sylvan::Bdd forwardSet = nodes;
  skelStack.push(forwardSet);

  sylvan::Bdd forwardFront = nodes;
  sylvan::Bdd forwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

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

  sylvan::Bdd layer = skelStack.top();
  skelStack.pop();
  sylvan::Bdd newStartNode = pick(layer, cube);
  sylvan::Bdd newSkeleton = newStartNode;
  while(!skelStack.empty()) {
    layer = skelStack.top();
    skelStack.pop();

    sylvan::Bdd relPrevSkel = leaf_false();
    for(int i = 0 ; i < relationDeque.size(); i++) {
      sylvan::Bdd currentRelation = relationDeque[i].relationBdd;
      sylvan::BddSet currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultBack = intersectBdd(newSkeleton.RelPrev(currentRelation, currentRelationCube), nodeSet);
      symbolicSteps = symbolicSteps + 1;

      relPrevSkel = unionBdd(relPrevSkel, relResultBack);
    }

    sylvan::Bdd prevIntersectLayer = intersectBdd(relPrevSkel, layer);
    sylvan::Bdd pickNodeFromPrev = pick(prevIntersectLayer, cube);
    newSkeleton = unionBdd(newSkeleton, pickNodeFromPrev);
  }

  std::pair<sylvan::Bdd, sylvan::Bdd> forwardSkel = {forwardSet, newSkeleton};
  std::pair<sylvan::Bdd, int> nodeSteps = {newStartNode, symbolicSteps};
  std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, std::pair<sylvan::Bdd, int>> res = {forwardSkel, nodeSteps};
  return res;
}

//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
// BDD Sizes
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////

//Takes a best so far BDD size and a new BDD to test against
//Returns either the size of the new BDD or the best so far size, depending on which is bigger
unsigned long long findLargestBdd(sylvan::Bdd bdd, unsigned long long peak) {
  unsigned long long newVal = bdd.NodeCount();
  if(newVal > peak) {
    return newVal;
  }
  return peak;
}

//LOCKSTEP SATURATION ITERATIVE ##########################################################################
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturationBDDSize(const Graph &fullGraph) {
  /*auto start = std::chrono::high_resolution_clock::now();
  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);*/

  unsigned long long peakBdd = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
    return result;
  }

  //Things pulled out from while-loop
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    int relFrontI = 0;
    sylvan::Bdd relFront = relationDeque[relFrontI].relationBdd;
    sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

    int relBackI = 0;
    sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
    sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

    //Expand both forward and backward sets until one converges
    while(relFrontI < relationDeque.size() && relBackI < relationDeque.size()) {
      //Find images
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);

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
      //peakBdd = findLargestBdd(forwardSet, peakBdd);
      peakBdd = findLargestBdd(backwardSet, peakBdd);
    }

    //Save the set that has converged and the one that didn't
    bool frontConverged = relFrontI == relationDeque.size();
    sylvan::Bdd converged = frontConverged ? forwardSet : backwardSet;
    sylvan::Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

    //Throw away the elements from the nonConverged set that won't be part of the SCC
    nonConverged = intersectBdd(converged, nonConverged);
    if(frontConverged) {
      backwardSet = nonConverged;
    } else {
      forwardSet = nonConverged;
    }

    while(relFrontI < relationDeque.size()) {
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), backwardSet), forwardSet);
      if(relResultFront == leaf_false()) {
        relFrontI++;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      } else {
        relFrontI = 0;
        relFront = relationDeque[0].relationBdd;
        relFrontCube = relationDeque[0].cube;
        forwardSet = unionBdd(forwardSet, relResultFront);
        //peakBdd = findLargestBdd(forwardSet, peakBdd);
      }
    }

    while(relBackI < relationDeque.size()) {
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), forwardSet), backwardSet);
      if(relResultBack == leaf_false()) {
        relBackI++;
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      } else {
        relBackI = 0;
        relBack = relationDeque[0].relationBdd;
        relBackCube = relationDeque[0].cube;
        backwardSet = unionBdd(backwardSet, relResultBack);
        peakBdd = findLargestBdd(backwardSet, peakBdd);
      }
    }

    //Create SCC
    sylvan::Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
  return result;
}

//LOCKSTEP RELATION UNION ITERATIVE ##########################################################################
std::pair<std::list<sylvan::Bdd>, int> lockstepRelationUnionBDDSize(const Graph &fullGraph) {
  unsigned long long peakBdd = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
    return result;
  }

  //Things pulled out from while-loop
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    //This is the "ring" that we find the next ring from
    sylvan::Bdd forwardFront = v;
    sylvan::Bdd backwardFront = v;

    //This is the accumulator for the next ring
    sylvan::Bdd forwardAcc = leaf_false();
    sylvan::Bdd backwardAcc = leaf_false();

    sylvan::Bdd relResultFront;
    sylvan::Bdd relResultBack;

    sylvan::Bdd currentRelation;
    sylvan::BddSet currentRelationCube;

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
        sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
        sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
        peakBdd = findLargestBdd(forwardFront, peakBdd);
        peakBdd = findLargestBdd(backwardFront, peakBdd);
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
    sylvan::Bdd converged = frontConverged ? forwardSet : backwardSet;
    sylvan::Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

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
          sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), backwardSet), forwardSet);
          peakBdd = findLargestBdd(forwardFront, peakBdd);
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
          sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), forwardSet), backwardSet);
          peakBdd = findLargestBdd(backwardFront, peakBdd);
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
    sylvan::Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to SCC list
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using saturation
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relFrontI = 0;
  sylvan::Bdd relFront = relationDeque[relFrontI].relationBdd;
  sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

  unsigned long long peakBdd = 0;

  while(relFrontI < relationDeque.size()) {
    sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
    peakBdd = findLargestBdd(forwardSet, peakBdd);

    if(relResultFront == leaf_false()) {
      relFrontI++;
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    } else {
      relFrontI = 0;
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    }

	  //Add to the forward set
    forwardSet = unionBdd(forwardSet, relResultFront);
  }

  std::pair<sylvan::Bdd, int> result = {forwardSet, peakBdd};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using saturation
std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd backwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relBackI = 0;
  sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
  sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

  unsigned long long peakBdd = 0;

  while(relBackI < relationDeque.size()) {
  //Find images
    sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
    peakBdd = findLargestBdd(backwardSet, peakBdd);

    if(relResultBack == leaf_false()) {
      relBackI++;
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    } else {
      relBackI = 0;
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    }

    //Add to the forward and backward sets
    backwardSet = unionBdd(backwardSet, relResultBack);
  }

  std::pair<sylvan::Bdd, int> result = {backwardSet, peakBdd};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturationBDDSize(const Graph &fullGraph) {
  unsigned long long peakBdd = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardSaturationBDDSize(workingGraph, backwardSet);
    backwardSet = res2.first;
    if(res2.second > peakBdd){
      peakBdd = res2.second;
    }

    workingGraph.nodes = backwardSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardSaturationBDDSize(workingGraph, forwardSet);
    forwardSet = res1.first;
    /*if(res1.second > peakBdd) {
      peakBdd = res1.second;
    }*/

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(backwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, backwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using relation union
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  sylvan::Bdd forwardFront = nodes;
  sylvan::Bdd forwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

  unsigned long long peakBdd = 0;


  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardFront.RelNext(currentRelation, currentRelationCube), nodeSet), forwardSet);
      peakBdd = findLargestBdd(forwardFront, peakBdd);
      forwardAcc = unionBdd(forwardAcc, relResultFront);
    }

    if(forwardAcc != leaf_false()) {
      somethingChanged = true;
    }
    forwardSet = unionBdd(forwardSet, forwardAcc);

    forwardFront = differenceBdd(forwardAcc, forwardFront);
    forwardAcc = leaf_false();
  }
  std::pair<sylvan::Bdd, int> result = {forwardSet, peakBdd};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using relation union
std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd backwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  sylvan::Bdd backwardFront = nodes;
  sylvan::Bdd backwardAcc = leaf_false();
  sylvan::Bdd relResultFront;

  sylvan::Bdd currentRelation;
  sylvan::BddSet currentRelationCube;

  unsigned long long peakBdd = 0;

  bool somethingChanged = true;
  while(somethingChanged) {
    somethingChanged = false;

    for(int i = 0 ; i < relationDeque.size(); i++) {
      currentRelation = relationDeque[i].relationBdd;
      currentRelationCube = relationDeque[i].cube;

      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
      peakBdd = findLargestBdd(backwardFront, peakBdd);
      backwardAcc = unionBdd(backwardAcc, relResultFront);
    }

    if(backwardAcc != leaf_false()) {
      somethingChanged = true;
    }
    backwardSet = unionBdd(backwardSet, backwardAcc);

    backwardFront = differenceBdd(backwardAcc, backwardFront);
    backwardAcc = leaf_false();
  }

  std::pair<sylvan::Bdd, int> result = {backwardSet, peakBdd};
  return result;
}

std::pair<std::list<sylvan::Bdd>, int> xieBeerelRelationUnionBDDSize(const Graph &fullGraph) {
  unsigned long long peakBdd = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();


  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardRelationUnionBDDSize(workingGraph, backwardSet);
    backwardSet = res2.first;
    if(res2.second > peakBdd) {
      peakBdd = res2.second;
    }

    workingGraph.nodes = backwardSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardRelationUnionBDDSize(workingGraph, forwardSet);
    forwardSet = res1.first;
    if(res1.second > peakBdd) {
      peakBdd = res1.second;
    }

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(backwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, backwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, (int)peakBdd};
  return result;
}



//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
// OPTIMIZED SATURATION
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////


//Takes a list of relations, and some relation R to find overlap with
//Finds the first relation, starting from R1, that overlaps with R, returning R if none before do
int findFirstOverlap(int relI, std::deque<Relation> relationDeque) {
  int rel = relI;
  for(int i = 0 ; i < relI ; i++) {
      if(relationDeque[relI].bottom < relationDeque[i].top) {
        continue;
      } else {
        rel = i;
        break;
      }
  }
  return rel;
}

//LOCKSTEP SATURATION ITERATIVE OPTIMIZED ##########################################################################
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturationOptimized(const Graph &fullGraph) {
  /*auto start = std::chrono::high_resolution_clock::now();
  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);*/

  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  //Things pulled out from while-loop
  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    int relFrontI = 0;
    sylvan::Bdd relFront = relationDeque[relFrontI].relationBdd;
    sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

    int relBackI = 0;
    sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
    sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

    //Expand both forward and backward sets until one converges
    while(relFrontI < relationDeque.size() && relBackI < relationDeque.size()) {
      //Find images
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
      symbolicSteps = symbolicSteps + 2;

      //Update relations
      if(relResultFront == leaf_false()) {
        relFrontI++;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      } else {
        relFrontI = findFirstOverlap(relFrontI, relationDeque);
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      }
      if(relResultBack == leaf_false()) {
        relBackI++;
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      } else {
        relBackI = findFirstOverlap(relBackI, relationDeque);
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      }

      //Add to the forward and backward sets
      forwardSet = unionBdd(forwardSet, relResultFront);
      backwardSet = unionBdd(backwardSet, relResultBack);
    }

    //Save the set that has converged and the one that didn't
    bool frontConverged = relFrontI == relationDeque.size();
    sylvan::Bdd converged = frontConverged ? forwardSet : backwardSet;
    sylvan::Bdd nonConverged = frontConverged ? backwardSet : forwardSet;

    //Throw away the elements from the nonConverged set that won't be part of the SCC
    nonConverged = intersectBdd(converged, nonConverged);
    if(frontConverged) {
      backwardSet = nonConverged;
    } else {
      forwardSet = nonConverged;
    }


    while(relFrontI < relationDeque.size()) {
      sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), backwardSet), forwardSet);
      symbolicSteps++;
      if(relResultFront == leaf_false()) {
        relFrontI++;
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
      } else {
        relFrontI = findFirstOverlap(relFrontI, relationDeque);
        relFront = relationDeque[relFrontI].relationBdd;
        relFrontCube = relationDeque[relFrontI].cube;
        forwardSet = unionBdd(forwardSet, relResultFront);
      }
    }

    while(relBackI < relationDeque.size()) {
      sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), forwardSet), backwardSet);
      symbolicSteps++;
      if(relResultBack == leaf_false()) {
        relBackI++;
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
      } else {
        relBackI = findFirstOverlap(relBackI, relationDeque);
        relBack = relationDeque[relBackI].relationBdd;
        relBackCube = relationDeque[relBackI].cube;
        backwardSet = unionBdd(backwardSet, relResultBack);
      }
    }

    //Create SCC
    sylvan::Bdd scc = frontConverged ? backwardSet : forwardSet;
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(converged, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, converged);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  //Return SCC list and number of symbolic steps
  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

//XIE-BEEREL SATURATION ITERATIVE OPTIMIZED ##########################################################################
std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturationOptimized(const Graph &fullGraph) {
  int symbolicSteps = 0;

  std::stack<sylvan::Bdd> callStack;
  callStack.push(fullGraph.nodes);

  std::list<sylvan::Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
    return result;
  }

  const sylvan::BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;
  workingGraph.nodes = leaf_false();

  while(!callStack.empty()) {
    const sylvan::Bdd nodeSet = callStack.top();
    callStack.pop();

    sylvan::Bdd v = pick(nodeSet, fullCube);
    sylvan::Bdd forwardSet = v;
    sylvan::Bdd backwardSet = v;

    workingGraph.nodes = nodeSet;

    std::pair<sylvan::Bdd, int> res2 = reachabilityBackwardSaturationOpt(workingGraph, backwardSet);
    backwardSet = res2.first;
    symbolicSteps = symbolicSteps + res2.second;

    workingGraph.nodes = backwardSet;

    std::pair<sylvan::Bdd, int> res1 = reachabilityForwardSaturationOpt(workingGraph, forwardSet);
    forwardSet = res1.first;
    symbolicSteps = symbolicSteps + res1.second;

    //Create SCC
    sylvan::Bdd scc = intersectBdd(forwardSet, backwardSet);
    //Add scc to scclist
    sccList.push_back(scc);

    //Emulating recursive calls by pushing to the stack
    //"Call" 1
    sylvan::Bdd recBdd1 = differenceBdd(backwardSet, scc);
    if(recBdd1 != leaf_false()) {
      callStack.push(recBdd1);
    }

    //"Call" 2
    sylvan::Bdd recBdd2 = differenceBdd(nodeSet, backwardSet);
    if(recBdd2 != leaf_false()) {
      callStack.push(recBdd2);
    }
  }

  std::pair<std::list<sylvan::Bdd>, int> result = {sccList, symbolicSteps};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using saturation
std::pair<sylvan::Bdd, int> reachabilityForwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd forwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relFrontI = 0;
  sylvan::Bdd relFront = relationDeque[relFrontI].relationBdd;
  sylvan::BddSet relFrontCube = relationDeque[relFrontI].cube;

  int symbolicSteps = 0;


  while(relFrontI < relationDeque.size()) {

    sylvan::Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
    symbolicSteps++;

    if(relResultFront == leaf_false()) {
      relFrontI++;
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    } else {
      relFrontI = findFirstOverlap(relFrontI, relationDeque);
      relFront = relationDeque[relFrontI].relationBdd;
      relFrontCube = relationDeque[relFrontI].cube;
    }

	  //Add to the forward set
    forwardSet = unionBdd(forwardSet, relResultFront);
  }

  std::pair<sylvan::Bdd, int> result = {forwardSet, symbolicSteps};
  return result;
}

//Computes the nodes reachable from the node(s) in the Graph given using saturation
std::pair<sylvan::Bdd, int> reachabilityBackwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes) {
  sylvan::BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  sylvan::Bdd backwardSet = nodes;
  sylvan::Bdd nodeSet = graph.nodes;

  int relBackI = 0;
  sylvan::Bdd relBack = relationDeque[relBackI].relationBdd;
  sylvan::BddSet relBackCube = relationDeque[relBackI].cube;

  int symbolicSteps = 0;

  while(relBackI < relationDeque.size()) {
  //Find images
    sylvan::Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
    symbolicSteps++;

    if(relResultBack == leaf_false()) {
      relBackI++;
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    } else {
      relBackI = findFirstOverlap(relBackI, relationDeque);
      relBack = relationDeque[relBackI].relationBdd;
      relBackCube = relationDeque[relBackI].cube;
    }

    //Add to the forward and backward sets
    backwardSet = unionBdd(backwardSet, relResultBack);
  }

  std::pair<sylvan::Bdd, int> result = {backwardSet, symbolicSteps};
  return result;
}