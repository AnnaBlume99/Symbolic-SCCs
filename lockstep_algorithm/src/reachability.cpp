#include<stack>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "reachability.h"
#include "bdd_utilities.h"

using sylvan::Bdd;
using sylvan::BddSet;

ReachResult createReachResult(const Bdd &set, const int symbolicSteps) {
  ReachResult result = {};
  result.set = set;
  result.symbolicSteps = symbolicSteps;
  return result;
}

ReachResult RelationUnion::forwardSet(const Graph &graph, const Bdd &nodes) {
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

    if(forwardAcc != leaf_false()) {
    somethingChanged = true;
    }
    forwardSet = unionBdd(forwardSet, forwardAcc);

    forwardFront = differenceBdd(forwardAcc, forwardFront);
    forwardAcc = leaf_false();
  }

  return createReachResult(forwardSet, symbolicSteps);
}

ReachResult RelationUnion::backwardSet(const Graph &graph, const Bdd &nodes) {
  std::deque<Relation> relationDeque = graph.relations;

  Bdd backwardSet = nodes;
  Bdd nodeSet = graph.nodes;

  Bdd backwardFront = nodes;
  Bdd backwardAcc = leaf_false();
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

      Bdd relResultFront = differenceBdd(intersectBdd(backwardFront.RelPrev(currentRelation, currentRelationCube), nodeSet), backwardSet);
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

  return createReachResult(backwardSet, symbolicSteps);
}

ChainResult RelationUnion::forwardSetLastLayer(const Graph &graph, const Bdd &nodes) {
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

SkeletonResult RelationUnion::forwardSkeleton(const Graph &graph, const Bdd &nodes) {
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
  Bdd newStartNode = pickAssignment(layer, cube);
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
    Bdd pickNodeFromPrev = pickAssignment(prevIntersectLayer, cube);
    newSkeleton = unionBdd(newSkeleton, pickNodeFromPrev);
  }

  SkeletonResult result = {};
  result.forwardSet = forwardSet;
  result.skeleton = newSkeleton;
  result.node = newStartNode;
  result.symbolicSteps = symbolicSteps;
  return result;
}







ReachResult Saturation::forwardSet(const Graph &graph, const Bdd &nodes) {
  BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  Bdd forwardSet = nodes;
  Bdd nodeSet = graph.nodes;

  int relFrontI = 0;
  Bdd relFront = relationDeque[relFrontI].relationBdd;
  BddSet relFrontCube = relationDeque[relFrontI].cube;

  int symbolicSteps = 0;

  while(relFrontI < relationDeque.size()) {
    Bdd relResultFront = differenceBdd(intersectBdd(forwardSet.RelNext(relFront, relFrontCube), nodeSet), forwardSet);
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

  return createReachResult(forwardSet, symbolicSteps);
}

ReachResult Saturation::backwardSet(const Graph &graph, const Bdd &nodes) {
  BddSet cube = graph.cube;
  std::deque<Relation> relationDeque = graph.relations;

  Bdd backwardSet = nodes;
  Bdd nodeSet = graph.nodes;

  int relBackI = 0;
  Bdd relBack = relationDeque[relBackI].relationBdd;
  BddSet relBackCube = relationDeque[relBackI].cube;

  int symbolicSteps = 0;

  while(relBackI < relationDeque.size()) {
  //Find images
    Bdd relResultBack = differenceBdd(intersectBdd(backwardSet.RelPrev(relBack, relBackCube), nodeSet), backwardSet);
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

  return createReachResult(backwardSet, symbolicSteps);
}