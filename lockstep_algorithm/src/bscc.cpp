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


//Our "real" version we made friday (untouched from then)
SccResult chainAlgBottomAdvancedReal(const Graph &fullGraph) {
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
    ChainResult transForward = rel.forwardSetLastLayer(workingGraph, startNode);
    symbolicSteps = symbolicSteps + transForward.symbolicSteps;

    //While-loop setup
    bool bottomSCC = false;
    ChainResult currentForward = transForward;
    Bdd bscc;
    Bdd v2;

    if(transForward.lastLayer == leaf_false()) { //This only happens if the SCC is a one node BSCC
      bottomSCC = true;
      bscc = startNode; 
      sccList.push_back(bscc);
    } else {
      v2 = pick(transForward.lastLayer, fullCube);
    }

    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      workingGraph.nodes = currentForward.forwardSet;
      ChainResult newForward = rel.forwardSetLastLayer(workingGraph, v2);
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
        currentForward = newForward;
        currentForward.forwardSet = differenceBdd(currentForward.forwardSet, scc);
        currentForward.lastLayer = differenceBdd(currentForward.lastLayer, scc);
        if(currentForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          v2 = pick(currentForward.forwardSet, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(currentForward.lastLayer, fullCube);
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
    const Bdd recBdd2 = differenceBdd(nodeSet, unionBdd(transForward.forwardSet, bsccBasin));
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);

}







//Version where we do not treat the first iteration any different to the next ones
SccResult chainAlgBottomAdvanced(const Graph &fullGraph) {
  //This is not necessary, but I am damnit trying to eliminate sources of the error....
  Bdd totalBasin = leaf_false();


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
    ChainResult currentForward;
    ChainResult transForward;
    Bdd bscc;
    Bdd v2;

    workingGraph.nodes = nodeSet;
    v2 = startNode;   

    bool firstForward = true;
    //WHILE-SEARCH
    while(!bottomSCC) {
      //Compute FWD in the current forward set from a node in the last layer
      ChainResult newForward = rel.forwardSetLastLayer(workingGraph, v2);
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
        currentForward = newForward;
        currentForward.forwardSet = differenceBdd(currentForward.forwardSet, scc);
        currentForward.lastLayer = differenceBdd(currentForward.lastLayer, scc);
        workingGraph.nodes = currentForward.forwardSet;
        if(currentForward.lastLayer == leaf_false()) {
          //lastLayer is empty - pick next pivot v2 from the forward set instead
          v2 = pick(currentForward.forwardSet, fullCube);
        } else {
          //lastLayer not empty - pick next pivot v2 from it
          v2 = pick(currentForward.lastLayer, fullCube);
        }        
      }
    }

    //Restore the workinggraph to be the original FWD since the basin of the bscc might reach anything in this scc-closed set
    //workingGraph.nodes = nodeSet;
    workingGraph.nodes = allNodes;
    ReachResult basinReach = rel.backwardSet(workingGraph, bscc);
    Bdd bsccBasin = basinReach.set;
    symbolicSteps = symbolicSteps + basinReach.symbolicSteps;
    totalBasin = unionBdd(totalBasin, bsccBasin);

    //Create "recursive" calls
    //"Call" 1 on FWD (original FWD before while-loop) \ bsccBasin, picking from lastLayer \ bsccBasin (or everything)
    const Bdd recBdd1 = differenceBdd(transForward.forwardSet, totalBasin);
    if(recBdd1 != leaf_false()) {
      const Bdd recNodeSet1 = differenceBdd(transForward.lastLayer, totalBasin);
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
    const Bdd recBdd2 = differenceBdd(nodeSet, unionBdd(transForward.forwardSet, totalBasin));
    if(recBdd2 != leaf_false()) {
      Bdd recNode2 = pick(recBdd2, fullCube);
      const std::pair<Bdd, Bdd> recPair2 = {recBdd2, recNode2};
      callStack.push(recPair2);
    }
  }

  //To print the BSCC's we output
  //printBddListAsString(workingGraph.cube.size(), sccList);

  //Return SCC list and number of symbolic steps
  return createSccResult(sccList, symbolicSteps);

}
