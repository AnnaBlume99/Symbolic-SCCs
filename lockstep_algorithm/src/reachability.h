#ifndef REACHABILITY_H
#define REACHABILITY_H

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "graph_creation.h"

struct ReachResult {
  sylvan::Bdd set;
  int symbolicSteps;
};

class RelationUnion {
  public:
    ReachResult forwardSet(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardSet(const Graph &graph, const sylvan::Bdd &nodes);
};

class Saturation {
  public:
    ReachResult forwardSet(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardSet(const Graph &graph, const sylvan::Bdd &nodes);
};

#endif //REACHABILITY_H