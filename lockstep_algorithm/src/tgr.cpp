#include <iostream>
#include <list>
#include <deque>
#include <stack>
#include <vector>
#include <chrono>
#include <set>
#include <queue>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "scc.h"
#include "bdd_utilities.h"
#include "print.h"
#include "bscc.h"

using sylvan::Bdd;
using sylvan::BddSet;

std::pair<std::vector<Bdd>,int> relationFireSets(const Graph &fullGraph) {
  int symbolicSteps = 0;
  RelationUnion reach;
  
  std::deque<Relation> relations = fullGraph.relations;
  std::vector<Bdd> fireSets;

  Graph workingGraph = {};
  workingGraph.nodes = fullGraph.nodes;
  workingGraph.cube = fullGraph.cube;

  for(Relation rel : relations) {
    std::deque<Relation> relDeque = {rel};
    workingGraph.relations = relDeque;
    ReachResult fwd = reach.forwardStepNoDiff(workingGraph, fullGraph.nodes);
    symbolicSteps += fwd.symbolicSteps;
    ReachResult fireSet = reach.backwardStepNoDiff(workingGraph, fwd.set); //Do we have self-loops? TODO: Figure out why it works with the difference version (originial backwardstep)
    symbolicSteps += fireSet.symbolicSteps;
    //printBdd(fireSet.set);
    fireSets.push_back(fireSet.set);
    //std::cout << "fireset:" << fireSet.set.SatCount(fullGraph.cube) << std::endl;
  }
  return {fireSets, symbolicSteps};
}

std::pair<Graph, int> reduce(Bdd &pivots, Graph &universe){
  int symbolicSteps = 0;
  Graph workingGraph;
  workingGraph.cube = universe.cube;
  workingGraph.nodes = universe.nodes;
  workingGraph.relations = universe.relations;

  RelationUnion rel;
  ReachResult fwdRes = rel.forwardSet(workingGraph, pivots);
  Bdd fwd = fwdRes.set;
  symbolicSteps += fwdRes.symbolicSteps;
  
  workingGraph.nodes = fwd;
  ReachResult bwd = rel.backwardSet(workingGraph, pivots);
  symbolicSteps += bwd.symbolicSteps;
  Bdd extendedComponent = bwd.set;
  Bdd bottom = differenceBdd(fwd, extendedComponent);

  if(universe.nodes != fwd) {
    //Workinggraph nodes already fwd.set
    ReachResult fwdBasin = rel.backwardSet(universe, fwd);
    Bdd basin = fwdBasin.set;
    symbolicSteps += fwdBasin.symbolicSteps;
    universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, fwd));
  }
  if(bottom != leaf_false()) {
    ReachResult bottomBasin = rel.backwardSet(universe, bottom);
    Bdd basin = bottomBasin.set;
    symbolicSteps += bottomBasin.symbolicSteps;
    universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, bottom));

  }
  return {universe, symbolicSteps};
}

std::pair<Graph, int> TGR(Graph &universe) {
  int symbolicSteps = 0;

  std::pair<std::vector<Bdd>,int> fireSetResult = relationFireSets(universe);
  std::vector<Bdd> fireSets = fireSetResult.first;
  Bdd currNodes = universe.nodes;
  symbolicSteps += fireSetResult.second;
  int noDeletions = 0;
  for(int i = 0; i < fireSets.size(); i++) {
    Bdd fireSet = fireSets[i];
    //printBdd(fireSet);
    if(intersectBdd(fireSet, universe.nodes) == leaf_false()){
      //std::cout << i<<"Deleting 1 on place" << i- noDeletions << "with " << noDeletions <<" deletions" << std::endl;
      //This is possible.. right?
      universe.relations.erase(universe.relations.begin() + i - noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
      noDeletions++;
      continue;
    }
    std::pair<Graph, int> reduceRes = reduce(fireSet, universe);
    universe = reduceRes.first;
    symbolicSteps += reduceRes.second;
    if(intersectBdd(fireSet, universe.nodes) == leaf_false()){
      //std::cout << "Deleting 2 on place" << i- noDeletions << "with " << noDeletions <<" deletions" << std::endl;
      universe.relations.erase(universe.relations.begin()+i-noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
      noDeletions++;
    }
  }
  std::cout << "Returning universe with " << universe.relations.size() << " relations left" << std::endl;
  std::cout << "And " << universe.nodes.SatCount(universe.cube) << " nodes left " << std::endl;
  return {universe, symbolicSteps};
}

struct ITGRWorker {
  long long weight;
  bool forwardPhase;
  Bdd fwd;
  Bdd component;
  Bdd front;
  int index;
};

class Comparator{
  public:
    bool operator()(ITGRWorker &a, ITGRWorker &b){
      return a.weight > b.weight;
    }
};

void printQueueStatus(const std::priority_queue<ITGRWorker, std::vector<ITGRWorker>, Comparator> &pq){
  std::priority_queue<ITGRWorker, std::vector<ITGRWorker>, Comparator> p = pq;
  std::cout << "Queue size:" << p.size() << std::endl;
  while(!p.empty()){
    std::cout << p.top().weight << ", ";
    p.pop();
  }
  std::cout << std::endl;
}

std::pair<Graph, int> ITGR(const Graph &graph) {
  int symbolicSteps = 0;

  Graph universe = {
    graph.nodes, graph.cube, graph.relations
  };

  std::pair<std::vector<Bdd>,int> fireSetResult = relationFireSets(universe);
  std::vector<Bdd> fireSets = fireSetResult.first;
  symbolicSteps += fireSetResult.second;

  std::priority_queue<ITGRWorker, std::vector<ITGRWorker>, Comparator> pq;

  //Initialize all worker processes and put them in the PQ
  for(int i = 0; i < fireSets.size(); i++) {
    Bdd fireSet = fireSets[i]; //Reach in pseudocode
    long long weight = fireSet.SatCount(universe.cube);
    ITGRWorker worker = {
      weight, //Weight for priority queue (size of the set)
      true, // Forward phase = true, ext phase = false
      fireSet, //FWD
      leaf_false(), //Component
      leaf_false(), //Not in use! (Will hopefully be front at some point)
      i //index
    };
    pq.push(worker);
  }

  RelationUnion rel;  
  std::vector<bool> removed(universe.relations.size(), false);

  int c = 0;
  while(!pq.empty()) {
    // if(c % 100 == 0) {
    //   printQueueStatus(pq);
    // }
    // c++;
    ITGRWorker w = pq.top();
    pq.pop();

    if(w.forwardPhase) {
      ReachResult fwdStep = rel.forwardStepNoDiff(universe, intersectBdd(universe.nodes, w.fwd));
      symbolicSteps += fwdStep.symbolicSteps;
      Bdd newFwd = unionBdd(w.fwd, fwdStep.set); 
      
      bool fixpoint = newFwd == w.fwd;
      if(fixpoint) {
        if(universe.nodes != newFwd) {
          ReachResult basin = rel.backwardSet(universe, newFwd);
          symbolicSteps += basin.symbolicSteps;
          universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin.set, newFwd));
        }

        //new worker -> next phase
        Bdd component = intersectBdd(fireSets[w.index], universe.nodes);
        long long newWeight = component.SatCount(universe.cube);
        ITGRWorker newWorker = {
          newWeight,
          false, //move to next phase
          newFwd, //the whole forward set
          component, //Component
          leaf_false(), //not in use
          w.index
        };
        pq.push(newWorker);
      } else {
        //new worker -> same phase
        long long newWeight = newFwd.SatCount(universe.cube);
        ITGRWorker newWorker = {
          newWeight,
          true, //stay in this phase
          newFwd, //fwd set being built
          leaf_false(), //Component
          leaf_false(), //not in use
          w.index
        };
        pq.push(newWorker);
      }
    } else {
      Graph workingGraph = { intersectBdd(w.fwd, universe.nodes), universe.cube, universe.relations };
      ReachResult bwdStep = rel.backwardStepNoDiff(workingGraph, w.component);
      symbolicSteps += bwdStep.symbolicSteps;
      Bdd newComponent = unionBdd(w.component, bwdStep.set);

      bool fixpoint = newComponent == w.component;
      if(fixpoint) {
        Bdd bottom = differenceBdd(intersectBdd(w.fwd, universe.nodes), newComponent);
        if(bottom != leaf_false()) {
          ReachResult basin = rel.backwardSet(universe, bottom);
          symbolicSteps += basin.symbolicSteps;
          universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin.set, bottom));
        }
        int i = w.index;
        if(intersectBdd(fireSets[i], universe.nodes) == leaf_false()){
          int noDeletions = 0;
          for(int j = 0; j < i; j++) {
            noDeletions += removed[j];
          }
          universe.relations.erase(universe.relations.begin()+i-noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
          removed[i] = true;
        }
      } else {
        long long newWeight = newComponent.SatCount(universe.cube);
        ITGRWorker newWorker = {
          newWeight,
          false, //stay in component phase
          w.fwd, //fwd set being built
          newComponent, //Component
          leaf_false(), //not in use
          w.index
        };
        pq.push(newWorker);
      }
    }
  }

  return {universe, symbolicSteps};
}

