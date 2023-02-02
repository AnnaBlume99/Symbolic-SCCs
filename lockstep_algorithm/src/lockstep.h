#ifndef LOCKSTEP_H
#define LOCKSTEP_H
#include <deque>
#include<list>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "petriTranslation.h"
#include "reachability.h"

struct SccResult {
  std::list<sylvan::Bdd> sccs;
  int symbolicSteps;
};

struct SkeletonResult {
  sylvan::Bdd forwardSet;
  sylvan::Bdd skeleton;
  sylvan::Bdd node;
  int symbolicSteps;
};

struct ChainResult {
  sylvan::Bdd forwardSet;
  sylvan::Bdd lastLayer;
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

//Skeleton algorithm
SccResult skeletonAlg(const Graph &fullGraph);

//Chain algorithm (new skeleton algorithm)
SccResult chainAlg(const Graph &fullGraph);

//Lockstep
SccResult lockstepSaturation(const Graph &fullGraph);
SccResult lockstepRelationUnion(const Graph &fullGraph);

//Xie-Beerel
SccResult xieBeerelSaturation(const Graph &fullGraph);
SccResult xieBeerelRelationUnion(const Graph &fullGraph);

//Reachability TODO: move to reachability.cpp
ChainResult reachabilityForwardRelationUnionLastLayer(const Graph &graph, const sylvan::Bdd &nodes);
SkeletonResult skeletonForward(const Graph &graph, const sylvan::Bdd &nodes);

#endif  //LOCKSTEP_H