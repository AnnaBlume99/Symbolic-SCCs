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

struct ChainResultData {
  sylvan::Bdd forwardSet;
  sylvan::Bdd lastLayer;
  int symbolicSteps;
  int forwardLayers;
  int lastLayerBreadth;
};


struct ReachResultBottom {
  sylvan::Bdd set;
  int symbolicSteps;
  bool isBscc;
};

//Reachability methods using the union of the relations
class RelationUnion {
  public:
    ReachResult forwardStep(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardStep(const Graph &graph, const sylvan::Bdd &nodes);

    ReachResult forwardSet(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardSet(const Graph &graph, const sylvan::Bdd &nodes);

    //Reachability for the Chain Algorithm
    ChainResult forwardSetLastLayer(const Graph &graph, const sylvan::Bdd &nodes);

    //Chain reachability with extra metadata for switching to XB when necessary
    ChainResultData forwardSetLastLayerData(const Graph &graph, const sylvan::Bdd &nodes);

    //Reachability for the Skeleton Algorithm
    SkeletonResult forwardSkeleton(const Graph &graph, const sylvan::Bdd &nodes);

    //Shortcutting forward-set for BSCCs
    ReachResultBottom forwardSetShortcut(const Graph &graph, const sylvan::Bdd &nodes, const sylvan::Bdd &backwardSet);

};

//Reachability methods using the saturation heuristic
class Saturation {
  public:
    ReachResult forwardSet(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardSet(const Graph &graph, const sylvan::Bdd &nodes);

    //Shortcutting forward-set for BSCCs
    ReachResultBottom forwardSetShortcut(const Graph &graph, const sylvan::Bdd &nodes, const sylvan::Bdd &backwardSet);
};

/*class Reach {
  public:
    ReachResult forwardSet(const Graph &graph, const sylvan::Bdd &nodes);
    ReachResult backwardSet(const Graph &graph, const sylvan::Bdd &nodes);
};*/

#endif //REACHABILITY_H