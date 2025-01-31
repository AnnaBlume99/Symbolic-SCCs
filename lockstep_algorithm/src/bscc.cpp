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
#include "tgr.h"
#include "deadlock.h"

using sylvan::Bdd;
using sylvan::BddSet;

//Version where we do not treat the first iteration any different to the next ones
SccResult chainAlgBottomAdvanced2(const Graph &fullGraph) {
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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet; 

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet; 

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
        transForward = newForward;
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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, v2);
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
  int spuriousSCCs = 0;

  std::list<Bdd> sccList = {};
  if(fullGraph.nodes == leaf_false()) {
    return createSccResult(sccList, symbolicSteps);
  }

  //TGR Testing:
  // std::pair<Graph, int> reducedGraph = TGR(fullGraph);
  // symbolicSteps += reducedGraph.second;

  // const Bdd allNodes = reducedGraph.first.nodes;
  // const BddSet fullCube = reducedGraph.first.cube;
  // const std::deque<Relation> relationDeque = reducedGraph.first.relations;
  //End TGR

  //Deadlock detection
  // std::pair<SccResult, Graph> dl = deadlockRemoval(fullGraph);
  // symbolicSteps += dl.first.symbolicSteps;
  // for(Bdd bs : dl.first.sccs){
  //   sccList.push_back(bs);
  // }
  // const Bdd allNodes1 = dl.second.nodes;
  // const BddSet fullCube1 = fullGraph.cube;
  // const std::deque<Relation> relationDeque1 = fullGraph.relations;
  // std::cout << ";" << sccList.size();
  // if(allNodes1 == leaf_false()) {
  //   std::cout << ";" << spuriousSCCs;
  //   return createSccResult(sccList, symbolicSteps);
  // }
  // //Deadlock detection end

  // //ITGR Testing:
  // const Graph deadlockGraph = { allNodes1, fullCube1, relationDeque1 };
  // std::pair<Graph, int> reducedGraph = ITGR(deadlockGraph);
  // symbolicSteps += reducedGraph.second;
  // const Bdd allNodes = reducedGraph.first.nodes;
  // const BddSet fullCube = reducedGraph.first.cube;
  // const std::deque<Relation> relationDeque = reducedGraph.first.relations;
  //End ITGR


  //Normal code
  const Bdd allNodes = fullGraph.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;
  //End Normal code

  

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;
    workingGraph.nodes = nodeSet; 

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
        spuriousSCCs++;

        //Not a BSCC, initialize next loop of while
        //Update the current forward set we work on and subtract the scc (which is not bscc) from the lastlayer and forwardset
        newForward.forwardSet = differenceBdd(newForward.forwardSet, scc);

        newForward.lastLayer = differenceBdd(newForward.lastLayer, scc);
        workingGraph.nodes = newForward.forwardSet;
        if(newForward.lastLayer == leaf_false()) {
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

  std::cout << ";" << spuriousSCCs;

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    //We find the first FWD* without finding the SCC
    workingGraph.nodes = nodeSet;
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, v2);
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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet;

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
          workingGraph.nodes = newForward.forwardSet;
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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    ChainResult transForward;
    Bdd bscc;
    workingGraph.nodes = nodeSet; 

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
          transForward = newForward; //Not needed
          firstForward = false;
        }

        if(oldForward == newForward.forwardSet) {
          forwardProgress = false;
        } else {
          oldForward = newForward.forwardSet;
          workingGraph.nodes = newForward.forwardSet;
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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    Bdd allScc = leaf_false(); //New for Cumulativebasin

    workingGraph.nodes = nodeSet;

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet;  

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet;

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
    Bdd v2 = std::get<1>(nodeSetAndStartNode);

    //While-loop setup
    bool bottomSCC = false;
    ChainResult newForward;
    Bdd bscc;

    workingGraph.nodes = nodeSet; 

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

  Bdd initNodes = initGraph.nodes;
  const BddSet fullCube = initGraph.cube;
  const std::deque<Relation> relationDeque = initGraph.relations;

  RelationUnion rel;

  Graph workingGraph = {};
  workingGraph.nodes = leaf_true();
  workingGraph.cube = fullCube;
  workingGraph.relations = relationDeque;

  //These are all the nodes from basin computations which should be removed
  Bdd deleteNodes = leaf_false();
  while(initNodes != leaf_false()) {
    //Setup the callstack
    //instead of making the first pick randomly, we can pick from lastlayer of the forward set
    std::stack<std::pair<Bdd, Bdd>> callStack;
    const Bdd startNode = pick(initNodes, fullCube);

    //Working graph should be all nodes minus the ones we have seen
    //Seen nodes will either be removed nodes or part of some other SCC closed call on the stack
    workingGraph.nodes = differenceBdd(leaf_true(), deleteNodes);
    const ChainResult initForwardSet = rel.forwardSetLastLayerInit(workingGraph, startNode, deleteNodes);
    symbolicSteps += initForwardSet.symbolicSteps;

    if(initForwardSet.forwardSet == leaf_false()) {
      initNodes = differenceBdd(initNodes, startNode);
      continue;
    }

    const std::pair<Bdd, Bdd> pushPair = {initForwardSet.forwardSet, pick(initForwardSet.lastLayer, fullCube)};
    callStack.push(pushPair);

    while(!callStack.empty()) {
      const std::pair<Bdd, Bdd> nodeSetAndStartNode = callStack.top();
      callStack.pop();
      Bdd nodeSet = std::get<0>(nodeSetAndStartNode);
      Bdd v2 = std::get<1>(nodeSetAndStartNode);

      //While-loop setup
      bool bottomSCC = false;
      ChainResult newForward;
      Bdd bscc;
      workingGraph.nodes = nodeSet;

      //WHILE-SEARCH
      while(!bottomSCC) {
        //Compute FWD in the current forward set from a node in the last layer
        workingGraph.nodes = differenceBdd(nodeSet, deleteNodes);
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
            //lastLayer is empty - pick next pivot v2 from the forward step instead
            ReachResult sccNext = rel.forwardStep(workingGraph, scc);
            symbolicSteps += sccNext.symbolicSteps;
            v2 = pick(sccNext.set, fullCube);
          } else {
            //lastLayer not empty - pick next pivot v2 from it
            v2 = pick(newForward.lastLayer, fullCube);
          }        
        }
      }

      //Restore the workinggraph to be the anything since the basin of the bscc might reach anything
      workingGraph.nodes = nodeSet;

      ReachResult basinReach = rel.backwardSet(workingGraph, bscc); //Stuck here *sad violin*

      symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
      Bdd bsccBasin = basinReach.set;

      //All nodes found from a basin are safe to remove
      deleteNodes = unionBdd(deleteNodes, bsccBasin);
      //we should only keep the initial nodes which have not been seen
      initNodes = differenceBdd(initNodes, deleteNodes);

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
  Bdd currentAll = allNodes;

  RelationUnion rel;
  
  //std::cout << "Approx list length:" << approx.size() << std::endl;
  
  for(Bdd bigBscc : approx) {
    bigBscc = intersectBdd(currentAll, bigBscc);
    if(bigBscc == leaf_false()) {
      continue;
    }

    workingGraph.nodes = bigBscc;

    //find BSCC in bigBscc
    Bdd startNode = pick(bigBscc, fullCube);
    ChainResult newForward;
    bool bottomSCC = false;
    Bdd bscc;

    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      newForward = rel.forwardSetLastLayer(workingGraph, startNode);
      symbolicSteps = symbolicSteps + newForward.symbolicSteps;

      //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
      workingGraph.nodes = newForward.forwardSet;
      const ReachResult transBackward = rel.backwardSet(workingGraph, startNode);
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
          startNode = pick(sccNext.set, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          startNode = pick(newForward.lastLayer, fullCube);
        }        
      }
    }
    //std::cout << "Done with for loop..." << std::endl;
    workingGraph.nodes = currentAll;
    ReachResult bsccBasinReach = rel.backwardSet(workingGraph, bscc);
    symbolicSteps += bsccBasinReach.symbolicSteps;
    Bdd bsccBasin = bsccBasinReach.set;
    currentAll = differenceBdd(currentAll, bsccBasin);
  }

  //call to normal chain, and add results before returning.
  Graph newGraph;
  newGraph.nodes = currentAll;
  newGraph.cube = fullCube;
  newGraph.relations = relationDeque;
  SccResult chainRes = chainAlgBottomSingleRecCall(newGraph);

  //std::cout << "Done with finding rest of bsccs..." << std::endl;

  //Return total SCC list and number of symbolic steps
  sccList.splice(sccList.end(), chainRes.sccs);
  return createSccResult(sccList, symbolicSteps + chainRes.symbolicSteps);
}

SccResult chainAlgBottomSingleRecCallProjExhaustive(const Graph &fullGraph, std::list<Bdd> &approx) {
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
  Bdd currentAll = allNodes;

  RelationUnion rel;
  
  for(Bdd bigBscc : approx) {
    bigBscc = intersectBdd(currentAll, bigBscc); //TODO: do we need this?
    if(bigBscc == leaf_false()) {
      continue;
    }

    while(bigBscc != leaf_false()) {
      workingGraph.nodes = bigBscc;

      //find BSCC in bigBscc
      Bdd startNode = pick(bigBscc, fullCube);
      ChainResult newForward;
      bool bottomSCC = false;
      Bdd bscc;

      while(!bottomSCC) {
        //Compute FWD in the current forward set from a node in the last layer
        newForward = rel.forwardSetLastLayer(workingGraph, startNode);
        symbolicSteps = symbolicSteps + newForward.symbolicSteps;

        //Compute the backward transitive closure on the result of FWD from last layer (result is the SCC)
        workingGraph.nodes = newForward.forwardSet;
        const ReachResult transBackward = rel.backwardSet(workingGraph, startNode);
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
            startNode = pick(sccNext.set, fullCube);
          } else {
            //lastLayer not empty - pick next pivot v2 from it
            startNode = pick(newForward.lastLayer, fullCube);
          }        
        }
      }

      workingGraph.nodes = currentAll;
      ReachResult bsccBasinReach = rel.backwardSet(workingGraph, bscc);
      symbolicSteps += bsccBasinReach.symbolicSteps;
      Bdd bsccBasin = bsccBasinReach.set;
      currentAll = differenceBdd(currentAll, bsccBasin);
      bigBscc = differenceBdd(bigBscc, bsccBasin);
    }
  }

  std::cout << ";" << sccList.size() << ";" << symbolicSteps;

  //call to normal chain, and add results before returning.
  Graph newGraph;
  newGraph.nodes = currentAll;
  newGraph.cube = fullCube;
  newGraph.relations = relationDeque;
  SccResult chainRes = chainAlgBottomSingleRecCall(newGraph);

  std::cout << ";" << chainRes.sccs.size() << ";" << chainRes.symbolicSteps;

  //Return total SCC list and number of symbolic steps
  sccList.splice(sccList.end(), chainRes.sccs);
  return createSccResult(sccList, symbolicSteps + chainRes.symbolicSteps);
}

Graph createApproximateGraph(const Graph &fullGraph) {
  const Bdd allNodes = fullGraph.nodes;
  const BddSet fullCube = fullGraph.cube;
  const std::deque<Relation> relationDeque = fullGraph.relations;

  std::deque<Relation> newRelations;

  Bdd currentRelation;
  BddSet currentRelationCube;
  for(int i = 0 ; i < relationDeque.size(); i++) {
    currentRelation = relationDeque[i].relationBdd;
    currentRelationCube = relationDeque[i].cube;

    //create new relation!
    Relation newRel = {};
    newRel.relationBdd = currentRelation;
    newRel.cube = fullCube;
    newRel.top = 0;
    newRel.bottom = 0;
    newRelations.push_back(newRel);
  }

  Graph newGraph = {};
  newGraph.nodes = allNodes;
  newGraph.cube = fullCube;
  newGraph.relations = newRelations;

  return newGraph;
}

//Version with only one recursive call given projections
SccResult xbBottomProj(const Graph &fullGraph, std::list<Bdd> &approx) {
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
  Bdd currentAll = allNodes;

  RelationUnion rel;

  for(Bdd bigBscc : approx) {
    bigBscc = intersectBdd(currentAll, bigBscc);
    if(bigBscc == leaf_false()) {
      continue;
    }

    bool bottomSCC = false;

    while(!bottomSCC) {
      workingGraph.nodes = currentAll;

      //find BSCC in bigBscc
      Bdd startNode = pick(bigBscc, fullCube);
      ReachResult basinReach = rel.backwardSet(workingGraph, startNode);
      symbolicSteps += basinReach.symbolicSteps;
      Bdd bsccBasin = basinReach.set;

      ReachResultBottom forwardReach = rel.forwardSetShortcut(workingGraph, startNode, bsccBasin);
      symbolicSteps += forwardReach.symbolicSteps;
      bool isBscc = forwardReach.isBscc;
      if(isBscc) {
        Bdd bscc = forwardReach.set;
        sccList.push_back(bscc);
      }
      bottomSCC = isBscc;
      
      currentAll = differenceBdd(currentAll, bsccBasin);
      bigBscc = differenceBdd(bigBscc, bsccBasin);
    }
  }

  //call to normal xb, and add results before returning.
  Graph newGraph;
  newGraph.nodes = currentAll;
  newGraph.cube = fullCube;
  newGraph.relations = relationDeque;
  SccResult xbRes = xieBeerelBottom<RelationUnion>(newGraph);

  //Return total SCC list and number of symbolic steps
  sccList.splice(sccList.end(), xbRes.sccs);
  return createSccResult(sccList, symbolicSteps + xbRes.symbolicSteps);
}

SccResult chainAlgBottomApproxPick(const Graph &fullGraph) {
  printRelationMatrix(fullGraph);
  Graph overApproximationGraph = createApproximateGraph(fullGraph);
  SccResult overApproxBdds = chainAlgBottomSingleRecCall(overApproximationGraph);

  SccResult realRes = chainAlgBottomSingleRecCallProjExhaustive(fullGraph, overApproxBdds.sccs);
  int symbolicSteps = overApproxBdds.symbolicSteps + realRes.symbolicSteps;
  return createSccResult(realRes.sccs, symbolicSteps); 
}

SccResult xbAlgBottomApproxPick(const Graph &fullGraph) {
  Graph overApproximationGraph = createApproximateGraph(fullGraph);
  SccResult overApproxBdds = xieBeerelBottom<RelationUnion>(overApproximationGraph);

  SccResult realRes = xbBottomProj(fullGraph, overApproxBdds.sccs);
  int symbolicSteps = overApproxBdds.symbolicSteps + realRes.symbolicSteps;

  return createSccResult(realRes.sccs, symbolicSteps); 
}

//MISC
void printCube(BddSet cube) {
  std::cout << "Cube size: " << cube.size() << ", with the following variables:" <<std::endl;
  std::vector<uint32_t> full = cube.toVector(); 
  for(uint32_t elem : full) {
    std::cout << elem << ", ";
  }
  std::cout << std::endl;
}

void printRelation(Relation rel) {
  std::cout << "------------------------------------------------------------" << std::endl;
  //std::cout << "Printing relation with top, bottom:" << rel.top << ", " << rel.bottom << std::endl;
  printCube(rel.cube);
  std::cout << "Bdd:" << std::endl;
  //printBdd(rel.relationBdd);
  printSingleRelationAsString(rel.relationBdd);
  std::cout << "------------------------------------------------------------" << std::endl;
}

void printRelationMatrix(const Graph &graph) {
  std::deque<Relation> rels = graph.relations;
  int n = rels.size();
  int v = graph.cube.size();
  int gridSize = n*v;
  int densityCounter = 0;
  std::vector<uint32_t> cubeVars = graph.cube.toVector();

  std::cout << "printRelationMatrix: Graph with " << n << " relations and" << v << " variables" << std::endl;
  std::string header = "> ";
  for(int i = 0; i < v; i++){
    if(i % 10 == 9) {
      header.append("O");
      continue;
    }
    header.append(" ");
  }

  std::cout << header << std::endl;
  for(int i = 0; i < n ; i++) {
    std::string cubeStr = "| ";
    Relation rel = rels[i];
    BddSet cube = rel.cube;
    for(uint32_t var : cubeVars){
      if(cube.contains(var)) {
        cubeStr.append("X");
        densityCounter++;
        goto skip;
      }
      cubeStr.append("-");
      skip:;
    }
    std::cout << cubeStr << std::endl;
  }
  std::cout << "Relation density: " << (float)densityCounter / (float)gridSize << std::endl;

}
