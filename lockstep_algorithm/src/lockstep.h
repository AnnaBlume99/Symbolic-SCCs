#ifndef LOCKSTEP_H
#define LOCKSTEP_H
#include <deque>
#include<list>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "petriTranslation.h"

struct SccResult {
  std::list<sylvan::Bdd> sccs;
  int symbolicSteps;
};

struct ReachResult {
  sylvan::Bdd set;
  int symbolicSteps;
};

/*
This contains:
- Iterative versions of SCC-finding algorithms lockstep and Xie Beerel, both with and without Saturation
- Functions for computing forward and backward sets
- Pick function
*/

//Old skeleton algorithm
SccResult oldSkeleton(const Graph &fullGraph);

//New skeleton algorithm
SccResult chain(const Graph &fullGraph);

//Lockstep
SccResult lockstepSaturation(const Graph &fullGraph);
SccResult lockstepRelationUnion(const Graph &fullGraph);

//Xie-Beerel
SccResult xieBeerelForwardSaturation(const Graph &fullGraph);
SccResult xieBeerelForwardRelationUnion(const Graph &fullGraph);
SccResult xieBeerelSaturation(const Graph &fullGraph);
SccResult xieBeerelRelationUnion(const Graph &fullGraph);

//Reachability
ReachResult reachabilityForwardSaturation(const Graph &graph, sylvan::Bdd nodes);
ReachResult reachabilityBackwardSaturation(const Graph &graph, sylvan::Bdd nodes);
ReachResult reachabilityForwardRelationUnion(const Graph &graph, sylvan::Bdd nodes);
ReachResult reachabilityBackwardRelationUnion(const Graph &graph, sylvan::Bdd nodes);
std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, int> reachabilityForwardRelationUnionLastLayer(const Graph &graph, sylvan::Bdd nodes);
std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, std::pair<sylvan::Bdd, int>> skeletonForward(const Graph &graph, sylvan::Bdd nodes);

//Pick a single node from a nodeSet
sylvan::Bdd pick(const sylvan::Bdd &nodeSet, const sylvan::BddSet &cube);

//BDD counting
SccResult lockstepRelationUnionBDDSize(const Graph &fullGraph);
SccResult lockstepSaturationBDDSize(const Graph &fullGraph);
SccResult xieBeerelSaturationBDDSize(const Graph &fullGraph);
SccResult xieBeerelRelationUnionBDDSize(const Graph &fullGraph);

std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes);

//Optimized saturation
SccResult lockstepSaturationOptimized(const Graph &fullGraph);
SccResult xieBeerelSaturationOptimized(const Graph &fullGraph);
ReachResult reachabilityForwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes);
ReachResult reachabilityBackwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes);

#endif  //LOCKSTEP_H