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

/*
This contains:
- Iterative versions of SCC-finding algorithms lockstep and Xie Beerel, both with and without Saturation
- Functions for computing forward and backward sets
- Pick function
*/

//Old skeleton algorithm
SccResult oldSkeleton(const Graph &fullGraph);

//New skeleton algorithm
std::pair<std::list<sylvan::Bdd>, int> newSkeleton(const Graph &fullGraph);

//Lockstep
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturation(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> lockstepRelationUnion(const Graph &fullGraph);

//Xie-Beerel
std::pair<std::list<sylvan::Bdd>, int> xieBeerelForwardSaturation(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelForwardRelationUnion(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturation(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelRelationUnion(const Graph &fullGraph);

//Reachability
std::pair<sylvan::Bdd, int> reachabilityForwardSaturation(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, int> reachabilityBackwardSaturation(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, int> reachabilityForwardRelationUnion(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, int> reachabilityBackwardRelationUnion(const Graph &graph, sylvan::Bdd nodes);
std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, int> reachabilityForwardRelationUnionLastLayer(const Graph &graph, sylvan::Bdd nodes);
std::pair<std::pair<sylvan::Bdd, sylvan::Bdd>, std::pair<sylvan::Bdd, int>> skeletonForward(const Graph &graph, sylvan::Bdd nodes);

//Pick a single node from a nodeSet
sylvan::Bdd pick(const sylvan::Bdd &nodeSet, const sylvan::BddSet &cube);

//BDD counting
std::pair<std::list<sylvan::Bdd>, int> lockstepRelationUnionBDDSize(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturationBDDSize(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturationBDDSize(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelRelationUnionBDDSize(const Graph &fullGraph);

std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardSaturationBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityBackwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, unsigned long long> reachabilityForwardRelationUnionBDDSize(const Graph &graph, sylvan::Bdd nodes);

//Optimized saturation
std::pair<std::list<sylvan::Bdd>, int> lockstepSaturationOptimized(const Graph &fullGraph);
std::pair<std::list<sylvan::Bdd>, int> xieBeerelSaturationOptimized(const Graph &fullGraph);
std::pair<sylvan::Bdd, int> reachabilityForwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes);
std::pair<sylvan::Bdd, int> reachabilityBackwardSaturationOpt(const Graph &graph, sylvan::Bdd nodes);

#endif  //LOCKSTEP_H