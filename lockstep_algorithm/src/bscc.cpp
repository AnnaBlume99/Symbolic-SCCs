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

using sylvan::Bdd;
using sylvan::BddSet;

//Version where we do not treat the first iteration any different to the next ones
SccResult chainAlgBottomAdvanced(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    bool firstForward = true;
    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;
      if(firstForward) {
        transForward = newForward;
        firstForward = false;
      }

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" calls
    //"Call" 1 on FWD (original FWD before while-loop) \ bsccBasin, picking from lastLayer \ bsccBasin (or everything)
    const Bdd recBdd1 = differenceBdd(transForward.forwardSet, bsccBasin);
    if(recBdd1 != leaf_false()) {
      const Bdd recNodeSet1 = differenceBdd(transForward.lastLayer, bsccBasin);
      Bdd recNode1;
      if(recNodeSet1 != leaf_false()) {
        //pick from lastLayer \ bsccBasin
        recNode1 = pick(recNodeSet1, fullCube);
      } else {
        //pick from FWD \ bsccBasin
        recNode1 = pick(recBdd1, fullCube);
      }
      const std::pair<Bdd, Bdd> recPair1 = {recBdd1, recNode1};
      callStack.push(recPair1);
    }

    //"Call" 2 on V \ (FWD U bsccBasin), picking from everything
    workingGraph.nodes = nodeSet;
    //We do a single BWD step from the recBdd1 = FWD \ bsccBasin in the full nodeset, since we might have edges going to this set, that we cannot see in the recursive call
    //Everything pointing to this will be safe to delete, since our rec calls are SCC closed and it therefore won't be bscc's
    //If there is such an edge, we remove the node's basin
    ReachResult stepBackBdd1 = rel.backwardStep(workingGraph, recBdd1);
    symbolicSteps = symbolicSteps + stepBackBdd1.symbolicSteps;

    const Bdd recBdd2_first_try = differenceBdd(nodeSet, unionBdd(transForward.forwardSet, bsccBasin));
    const Bdd outsideEdges = intersectBdd(recBdd2_first_try, stepBackBdd1.set);
    Bdd extraBasin = leaf_false();
    if(outsideEdges != leaf_false()) {
      ReachResult extraBasinReach = rel.backwardSet(workingGraph, outsideEdges); 
      symbolicSteps = symbolicSteps + extraBasinReach.symbolicSteps;
      extraBasin = extraBasinReach.set;
    }
    const Bdd recBdd2 = differenceBdd(recBdd2_first_try, extraBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call where we treat the first FWD differently
//by not finding the SCC and picking directly in lastLayer
SccResult chainAlgBottomSpecialFWD(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" calls
    //"Call" 1 on FWD (original FWD before while-loop) \ bsccBasin, picking from lastLayer \ bsccBasin (or everything)
    const Bdd recBdd1 = differenceBdd(transForward.forwardSet, bsccBasin);
    if(recBdd1 != leaf_false()) {
      const Bdd recNodeSet1 = differenceBdd(transForward.lastLayer, bsccBasin);
      Bdd recNode1;
      if(recNodeSet1 != leaf_false()) {
        //pick from lastLayer \ bsccBasin
        recNode1 = pick(recNodeSet1, fullCube);
      } else {
        //pick from FWD \ bsccBasin
        recNode1 = pick(recBdd1, fullCube);
      }
      const std::pair<Bdd, Bdd> recPair1 = {recBdd1, recNode1};
      callStack.push(recPair1);
    }

    //"Call" 2 on V \ (FWD U bsccBasin), picking from everything
    workingGraph.nodes = nodeSet;
    //We do a single BWD step from the recBdd1 = FWD \ bsccBasin in the full nodeset, since we might have edges going to this set, that we cannot see in the recursive call
    //Everything pointing to this will be safe to delete, since our rec calls are SCC closed and it therefore won't be bscc's
    //If there is such an edge, we remove the node's basin
    ReachResult stepBackBdd1 = rel.backwardStep(workingGraph, recBdd1);
    symbolicSteps = symbolicSteps + stepBackBdd1.symbolicSteps;

    const Bdd recBdd2_first_try = differenceBdd(nodeSet, unionBdd(transForward.forwardSet, bsccBasin));
    const Bdd outsideEdges = intersectBdd(recBdd2_first_try, stepBackBdd1.set);
    Bdd extraBasin = leaf_false();
    if(outsideEdges != leaf_false()) {
      ReachResult extraBasinReach = rel.backwardSet(workingGraph, outsideEdges); 
      symbolicSteps = symbolicSteps + extraBasinReach.symbolicSteps;
      extraBasin = extraBasinReach.set;
    }
    const Bdd recBdd2 = differenceBdd(recBdd2_first_try, extraBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call
SccResult chainAlgBottomSingleRecCall(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call where we treat the first FWD differently
//by not finding the SCC and picking directly in lastLayer
SccResult chainAlgBottomSingleRecSpecialFWD(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {

        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

/////////////////////////////// LOOP VERSIONS //////////////////////////////////////

//Version where we take FWD until it stops shrinking
SccResult chainAlgBottomForwardLoop(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    bool firstForward = true;
    //WHILE-SEARCH
    while(!bottomSCC) {
      bool forwardProgress = true;
      Bdd oldForward = leaf_false();

      while(forwardProgress) {
        //Compute FWD in the current forward set from a node in the last layer
        newForward = rel.forwardSetLastLayer(workingGraph, v2);
        symbolicSteps = symbolicSteps + newForward.symbolicSteps;
        if(firstForward) {
          transForward = newForward;
          firstForward = false;
        }

        if(oldForward == newForward.forwardSet) {
          forwardProgress = false;
        } else {
          oldForward = newForward.forwardSet;
          v2 = pick(newForward.lastLayer, fullCube);
        }
      }

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" calls
    //"Call" 1 on FWD (original FWD before while-loop) \ bsccBasin, picking from lastLayer \ bsccBasin (or everything)
    const Bdd recBdd1 = differenceBdd(transForward.forwardSet, bsccBasin);
    if(recBdd1 != leaf_false()) {
      const Bdd recNodeSet1 = differenceBdd(transForward.lastLayer, bsccBasin);
      Bdd recNode1;
      if(recNodeSet1 != leaf_false()) {
        //pick from lastLayer \ bsccBasin
        recNode1 = pick(recNodeSet1, fullCube);
      } else {
        //pick from FWD \ bsccBasin
        recNode1 = pick(recBdd1, fullCube);
      }
      const std::pair<Bdd, Bdd> recPair1 = {recBdd1, recNode1};
      callStack.push(recPair1);
    }

    //"Call" 2 on V \ (FWD U bsccBasin), picking from everything
    workingGraph.nodes = allNodes;
    ReachResult stepBackBdd1 = rel.backwardStep(workingGraph, recBdd1);
    symbolicSteps = symbolicSteps + stepBackBdd1.symbolicSteps;

    const Bdd recBdd2_first_try = differenceBdd(nodeSet, unionBdd(transForward.forwardSet, bsccBasin));
    ReachResult extraBasin = rel.backwardSet(workingGraph, intersectBdd(recBdd2_first_try, stepBackBdd1.set)); 
    symbolicSteps = symbolicSteps + extraBasin.symbolicSteps;
    const Bdd recBdd2 = differenceBdd(recBdd2_first_try, extraBasin.set);

    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call where we do a loop of FWD until it does not shrink anymore
SccResult chainAlgBottomSingleRecForwardLoop(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    bool firstForward = true;
    //WHILE-SEARCH
    while(!bottomSCC) {
      bool forwardProgress = true;
      Bdd oldForward = leaf_false();

      while(forwardProgress) {
        //Compute FWD in the current forward set from a node in the last layer
        newForward = rel.forwardSetLastLayer(workingGraph, v2);
        symbolicSteps = symbolicSteps + newForward.symbolicSteps;
        if(firstForward) {
          transForward = newForward;
          firstForward = false;
        }

        if(oldForward == newForward.forwardSet) {
          forwardProgress = false;
        } else {
          oldForward = newForward.forwardSet;
          v2 = pick(newForward.lastLayer, fullCube);
        }
      }

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

/////////////////////////////// DEADLOCK REMOVAL ///////////////////////////////////

std::pair<SccResult, Graph> deadlockRemoval(const Graph &fullGraph) {
  RelationUnion rel;
  int symbolicSteps = 0;
  Bdd nodes = fullGraph.nodes;
  std::list<Bdd> sccList = {};
  const BddSet fullCube = fullGraph.cube;

  ReachResult postAll = rel.forwardStep(fullGraph, nodes);
  symbolicSteps = symbolicSteps + postAll.symbolicSteps;
  Bdd post = postAll.set;

  ReachResult prePostAll = rel.backwardStep(fullGraph, post);
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

/////////////////////////// ADVANCED VERSIONS /////////////////////////////

//Version with only one recursive call and cumulative SCCs
SccResult chainAlgBottomSingleRecCallCumulative(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    Bdd allScc = leaf_false(); //New for Cumulativebasin

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      allScc = unionBdd(allScc, scc); //New for cumulativebasin

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, allScc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call collecting extra information
SccResult chainAlgBottomSingleRecCallExtra(const Graph &fullGraph) {
  int symbolicSteps = 0;
  int spuriousSccs = 0;
  long long nodesDiscovered = 0;

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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;
      nodesDiscovered += newForward.forwardSet.SatCount(fullCube);

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      nodesDiscovered += transBackward.set.SatCount(fullCube);
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        spuriousSccs++;
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          nodesDiscovered += sccNext.set.SatCount(fullCube);
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    nodesDiscovered += basinReach.set.SatCount(fullCube);
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call and switching
SccResult chainAlgBottomSingleRecCallSwitch(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    bool xbSwitch = false;
    Bdd switchBasin = leaf_false();
    long long setSize = nodeSet.SatCount(fullCube);

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      long long fwSize = newForward.forwardSet.SatCount(fullCube);
      float switch_ratio = 0.9;
      xbSwitch = ((float)fwSize / (float)setSize) >= switch_ratio;
      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      
      Bdd scc = leaf_false();
      if(xbSwitch){
        workingGraph.nodes = nodeSet;
        const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
        switchBasin = transBackward.set;
        symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
        scc = intersectBdd(switchBasin, newForward.forwardSet);
      } else {
        workingGraph.nodes = newForward.forwardSet;
        const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
        symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
        scc = transBackward.set;
      }

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        if(xbSwitch) {
          break;
        }

        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc
    //might reach anything in this scc-closed set
    Bdd bsccBasin = leaf_false();
    if(xbSwitch) {
      bsccBasin = switchBasin;
    } else {
      workingGraph.nodes = nodeSet;
      ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
      symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
      bsccBasin = basinReach.set;
    }

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

//Version with only one recursive call and switching
SccResult chainAlgBottomSingleRecCallSwitchAndBasin(const Graph &fullGraph) {
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
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    Bdd allScc = leaf_false(); //New for Cumulativebasin


    bool xbSwitch = false;
    Bdd switchBasin = leaf_false();
    long long setSize = nodeSet.SatCount(fullCube);

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      long long fwSize = newForward.forwardSet.SatCount(fullCube);
      float switch_ratio = 0.9;
      xbSwitch = ((float)fwSize / (float)setSize) >= switch_ratio;
      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      
      Bdd scc = leaf_false();
      if(xbSwitch){
        workingGraph.nodes = nodeSet;
        const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
        switchBasin = transBackward.set;
        symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
        scc = intersectBdd(switchBasin, newForward.forwardSet);
      } else {
        workingGraph.nodes = newForward.forwardSet;
        const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
        symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
        scc = transBackward.set;
      }
      allScc = unionBdd(allScc, scc); //New for cumulativebasin
      
      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        if(xbSwitch) {
          break;
        }

        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc
    //might reach anything in this scc-closed set
    Bdd bsccBasin = leaf_false();
    if(xbSwitch) {
      bsccBasin = switchBasin;
    } else {
      workingGraph.nodes = nodeSet;
      ReachResult basinReach = rel.backwardSet(workingGraph, allScc);
      symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
      bsccBasin = basinReach.set;
    }

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

///////////////////////////// INITIAL STATE VERSIONS /////////////////////////////////

//Version with only one recursive call which only knows Init at first
SccResult chainAlgBottomSingleRecCallInitState(const Graph &initGraph) {
  int symbolicSteps = 0;

  std::list<Bdd> sccList = {};
  if(initGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  const Bdd initNodes = initGraph.nodes;
  const BddSet fullCube = initGraph.cube;
  const std::deque<Relation> relationDeque = initGraph.relations;

  std::stack<std::pair<Bdd, Bdd>> callStack;
  const Bdd startNode = pick(initNodes, fullCube);
  const std::pair<Bdd, Bdd> pushPair = {initNodes, startNode};
  callStack.push(pushPair);
  
  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = leaf_true();
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  bool firstFwd = true;

  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;
      if(firstFwd) {
        firstFwd = false;
        nodeSet = newForward.forwardSet;
      }

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

///////////////////////////// Projections ////////////////////////////
//Version with only one recursive call given projections
SccResult chainAlgBottomSingleRecCallProj(const Graph &fullGraph, std::list<Bdd> &approx) {
  int symbolicSteps = 0;

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  if(approx.empty()) {
    return chainAlgBottomSingleRecCall(fullGraph);
  }

  const Bdd allNodes = fullGraph.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  Graph workingGraph = {};
  workingGraph.nodes = allNodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  RelationUnion rel;

  while(!approx.empty()) {
    Bdd bigBscc = approx.front();
    approx.pop_front();

    //find BSCC in bigBscc
    Bdd startNode = pick(bigBscc, fullCube);

    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    /////////////////////////////////////////

    approx.remove_if([](Bdd a){ return a.isZero(); });
  }

  //call to normal chain, and add results before returning.


  std::stack<std::pair<Bdd, Bdd>> callStack;
  const Bdd startNode = pick(allNodes, fullCube);
  const std::pair<Bdd, Bdd> pushPair = {allNodes, startNode};
  callStack.push(pushPair);
  
  while(!callStack.empty()) {
    const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
    callStack.pop();
    const Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
    const Bdd startNode = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      const Bdd scc = transBackward.set;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          symbolicSteps += sccNext.symbolicSteps;
          v2 = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(newForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    workingGraph.nodes = nodeSet;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    Bdd bsccBasin = basinReach.set;

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}