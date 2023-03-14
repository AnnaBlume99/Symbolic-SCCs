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

SccResult chainAlgBottomBasic(const Graph &fullGraph) {
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

    //Compute the forward transitive closure and keep the last layer of the computation
    workingGraph.nodes = nodeSet;
    const ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    const Bdd forwardSet = transForward.forwardSet;
    const Bdd lastForwardLayer = transForward.lastLayer;
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;

    //Compute the backward transitive closure on the result of forward (result is the SCC)
    workingGraph.nodes = forwardSet;
    const ReachResult transBackward = rel.backwardSet(workingGraph, startNode);
    const Bdd scc = transBackward.set;
    symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

    //Detect and report possible BSCC
    Bdd relNextScc = leaf_false();
    for(int i = 0 ; i < relationDeque.size(); i++) {
      Bdd currentRelation = relationDeque[i].relationBdd;
      BddSet currentRelationCube = relationDeque[i].cube;

      Bdd relResult = scc.RelNext(currentRelation, currentRelationCube);
      symbolicSteps = symbolicSteps + 1;

      relNextScc = unionBdd(relNextScc, relResult);
    }
    if(differenceBdd(relNextScc, scc) == leaf_false()) {
      //Report the BSCC
      sccList.push_back(scc);
    }

    //Create "recursive" calls
    //"Call" 1
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

    //"Call" 2
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
      const Bdd recNodeSet2 = intersectBdd(relPrevScc, recBdd2);
      Bdd recNode2;
      if(recNodeSet2 != leaf_false()) {
        recNode2 = pick(recNodeSet2, fullCube);
      } else {
        recNode2 = pick(recBdd2, fullCube);
      }
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }
  //printBddListAsString(workingGraph.cube.size(), sccList);
  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

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
      if(firstForward) {
        transForward = newForward;
        firstForward = false;
      }
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;   
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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
      if(firstForward) {
        transForward = newForward;
        firstForward = false;
      }
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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
  long long nodeCount = 0;
  int spuriousScc = 0;
  long long bsccSize = 0;

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
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;   
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;
    nodeCount += transForward.forwardSet.SatCount(fullCube);

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;
      nodeCount += newForward.forwardSet.SatCount(fullCube);

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      nodeCount += transBackward.set.SatCount(fullCube);
      spuriousScc++;
      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
        bsccSize += bscc.SatCount(fullCube);
      } else {

        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          ReachResult sccNext = rel.forwardStep(workingGraph, scc);
          nodeCount += sccNext.set.SatCount(fullCube);
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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    nodeCount += basinReach.set.SatCount(fullCube);

    //Create "recursive" call
    //"Call" on V \ bsccBasin, picking from everything
    const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }
  std::cout << ";" << spuriousScc << ";" << nodeCount;
  std::cout << ";" << bsccSize;

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}


//////////////////////////////////////////////////////////////////


//
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

//////////////////////////////////////////////////////////////////


//Version where we swith between XB and Chain behavior
SccResult chainAlgBottomSingleRecSwitchOld(const Graph &fullGraph) {
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
    ChainResultData newForward;
    Bdd bscc;
    Bdd v2;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResultData transForward = rel.forwardSetLastLayerData(workingGraph, startNode);
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;

    bool xb_behavior = false;
    //These are to check for changes over iterations and use this as basis for xb_behavior
    int oldForwardLayerCount = transForward.forwardLayers;
    int oldForwardLayerBreadth = transForward.forwardLayers;

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayerData(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //deal with data stuff

      //Magic constants
      int forwardLayerConstant = 50; //Probably in the range 10-100
      int lastLayerBreadthConstant = 40; //We don't rememeber any values here - we just have to test (maybe 10-100 as well)

      //Variable sizes
      bool layersSmaller = newForward.forwardLayers <= oldForwardLayerCount;
      oldForwardLayerCount = newForward.forwardLayers;
      bool breadthSmaller = newForward.lastLayerBreadth <= oldForwardLayerBreadth;
      oldForwardLayerBreadth = newForward.lastLayerBreadth;
      if(newForward.forwardLayers >= forwardLayerConstant) {
        xb_behavior = true;
      }

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

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

      if(xb_behavior) {
        bscc = scc;
        break;
      }
    }

    if(xb_behavior && !bottomSCC) {
      //find basin
      workingGraph.nodes = nodeSet;
      ReachResult res1 = rel.backwardSet(workingGraph, bscc);
      Bdd basin = res1.set;
      symbolicSteps = symbolicSteps + res1.symbolicSteps;

      //make "recursive" call
      Bdd recBdd = differenceBdd(nodeSet, basin);
      if(recBdd != leaf_false()) {
        Bdd recNode = pick(recBdd, fullCube);
        const std::pair<Bdd, Bdd> recPair = {recBdd, recNode};
        callStack.push(recPair);
      }
    } else {
      //Restore the workinggraph to be the original FWD since the basin of the bscc
      //might reach anything in this scc-closed set
      workingGraph.nodes = nodeSet;
      ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
      Bdd bsccBasin = basinReach.set;
      symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

      //Create "recursive" call
      //"Call" on V \ bsccBasin, picking from everything
      const Bdd recBdd = differenceBdd(nodeSet, bsccBasin);
      if(recBdd != leaf_false()) {
        Bdd recNode = pick(recBdd, fullCube);
        const std::pair<Bdd, Bdd> recPair = {recBdd, recNode};
        callStack.push(recPair);
      }
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}



SccResult chainAlgBottomCumulativeBasin(const Graph &fullGraph) {
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

    Bdd allScc = leaf_false();

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;  
    symbolicSteps = symbolicSteps + transForward.symbolicSteps; 

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      allScc = unionBdd(allScc, scc);

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
          //lastLayer is empty - pick next pivot v2 Post(SCC) instead
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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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

SccResult chainAlgBottomRunningBasin(const Graph &fullGraph) {
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
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;   

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        ReachResult sccBasin = rel.backwardSet(workingGraph, scc);
        symbolicSteps += sccBasin.symbolicSteps;
        
        newForward.forwardSet = differenceBdd(newForward.forwardSet, sccBasin.set);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, sccBasin.set);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 Post(SCC) instead
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
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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

SccResult chainAlgBottomCumulativeRunningBasin(const Graph &fullGraph) {
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

    Bdd allScc = leaf_false();

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;   
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, v2);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      const Bdd scc = transBackward.set;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;

      if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
      } else {
        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        ReachResult sccBasin = rel.backwardSet(workingGraph, scc);
        symbolicSteps += sccBasin.symbolicSteps;
        allScc = unionBdd(allScc, sccBasin.set);
        
        newForward.forwardSet = differenceBdd(newForward.forwardSet, sccBasin.set);
        newForward.lastLayer = differenceBdd(newForward.lastLayer, sccBasin.set);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 Post(SCC) instead
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
    ReachResult basinReach = rel.backwardSet(workingGraph, unionBdd(allScc, bscc));
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;

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




SccResult chainAlgBottomSingleRecSwitch(const Graph &fullGraph) {
  int symbolicSteps = 0;
  long long nodeCount = 0;
  int spuriousScc = 0;
  long long bsccSize = 0;

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
    bool xb_behavior = false;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    v2 = pick(transForward.lastLayer, fullCube);
    workingGraph.nodes = transForward.forwardSet;  
    long long fwSize = transForward.forwardSet.SatCount(fullCube);
    nodeCount += fwSize;
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;

    long long setSize = nodeSet.SatCount(fullCube);
    float switch_ratio = 0.9;
    bool condition = ((float)fwSize / (float)setSize) >= switch_ratio;
    if(condition) {
      //V1 where we find the BWD in FWD to find the SCC, and then the BWD from that
      //workingGraph.nodes = transForward.forwardSet;
      //ReachResult transBackward = rel.backwardSet(workingGraph, v2);

      //V2 where we find BWD of V2 and then intersect with FWD to hopefully save symbolic steps
      ReachResult transBackward = rel.backwardSet(workingGraph, v2);
      Bdd scc = intersectBdd(transBackward.set, transForward.forwardSet);
      nodeCount += transBackward.set.SatCount(fullCube);
      spuriousScc++;
      symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
      if(differenceBdd(transForward.forwardSet, scc) == leaf_false()) {
        //If BSCC, report the BSCC
        bottomSCC = true;
        bscc = scc;
        sccList.push_back(bscc);
        bsccSize += bscc.SatCount(fullCube);
      }
      //Create "recursive" call
      //"Call" on V \ bsccBasin, picking from everything
      const Bdd recBdd2 = differenceBdd(nodeSet, transBackward.set);
      if(recBdd2 != leaf_false()) {
        Bdd recNode2 = pick(recBdd2, fullCube);
        const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
        callStack.push(recPair2);
      }



    } else {
        
        //WHILE-SEARCH
        while(!bottomSCC) {
          //Compute FWD in the current forward set from a node in the last layer
          newForward = rel.forwardSetLastLayer(workingGraph, v2);
          symbolicSteps = symbolicSteps + newForward.symbolicSteps;
          nodeCount += newForward.forwardSet.SatCount(fullCube);

          //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
          workingGraph.nodes = newForward.forwardSet;
          const ReachResult transBackward = rel.backwardSet(workingGraph, v2);
          const Bdd scc = transBackward.set;
          symbolicSteps = symbolicSteps + transBackward.symbolicSteps;
          nodeCount += transBackward.set.SatCount(fullCube);
          spuriousScc++;
          if(differenceBdd(newForward.forwardSet, scc) == leaf_false()) {
            //If BSCC, report the BSCC
            bottomSCC = true;
            bscc = scc;
            sccList.push_back(bscc);
            bsccSize += bscc.SatCount(fullCube);
          } else {

            //Not a BSCC, initialize next loop of while
            //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
            newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);
            newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
            workingGraph.nodes = newForward.forwardSet;
            if(newForward.lastLayer == leaf_false()) {
              //lastLayer is empty - pick next pivot v2 from the forward set instead
              ReachResult sccNext = rel.forwardStep(workingGraph, scc);
              nodeCount += sccNext.set.SatCount(fullCube);
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
        Bdd bsccBasin = basinReach.set;
        symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
        nodeCount += basinReach.set.SatCount(fullCube);

        //Create "recursive" call
        //"Call" on V \ bsccBasin, picking from everything
        const Bdd recBdd2 = differenceBdd(nodeSet, bsccBasin);
        if(recBdd2 != leaf_false()) {
          Bdd recNode2 = pick(recBdd2, fullCube);
          const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
          callStack.push(recPair2);
        }
      }
    }

    
  std::cout << ";" << spuriousScc << ";" << nodeCount;
  std::cout << ";" << bsccSize;

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);
}

