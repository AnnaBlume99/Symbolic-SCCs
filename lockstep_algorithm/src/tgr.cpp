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
  workingGraph.relations = fullGraph.relations;

  for(Relation rel : relations) {
    std::deque<Relation> relDeque = {rel};
    workingGraph.relations = relDeque;
    ReachResult fwd = reach.forwardStep2(workingGraph, fullGraph.nodes);
    symbolicSteps += fwd.symbolicSteps;
    ReachResult fireSet = reach.backwardStep2(workingGraph, fwd.set); //Do we have self-loops? TODO: Figure out why it works with the difference version (originial backwardstep)
    symbolicSteps += fireSet.symbolicSteps;
    //printBdd(fireSet.set);
    fireSets.push_back(fireSet.set);
    //std::cout << "fireset:" << fireSet.set.SatCount(fullGraph.cube) << std::endl;
  }
  return {fireSets, symbolicSteps};
}

std::pair<Graph, int> reduce(Bdd pivots, Graph universe){
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

std::pair<Graph, int> TGR(Graph universe) {
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
    bool operator()(ITGRWorker a, ITGRWorker b){
      return a.weight > b.weight;
    }
};

std::pair<Graph, int> ITGR(Graph universe){
  int symbolicSteps = 0;
  
  BddSet fullCube = universe.cube;

  std::vector<bool> removed(universe.relations.size(), false);

  std::pair<std::vector<Bdd>,int> fireSetResult = relationFireSets(universe);
  std::vector<Bdd> fireSets = fireSetResult.first;
  symbolicSteps += fireSetResult.second;

  std::priority_queue<ITGRWorker, std::vector<ITGRWorker>, Comparator> pq;

  //Initialize all worker processes and put them in the PQ
  for(int i = 0; i < fireSets.size(); i++) {
    Bdd fireSet = fireSets[i];
    long long weight = fireSet.SatCount(fullCube);
    ITGRWorker worker = {
      weight,
      true,
      fireSet, //FWD
      leaf_false(), //Component
      fireSet, //Front
      i
    };
    pq.push(worker);
  }

  Graph workingGraph = {};
  workingGraph.nodes = universe.nodes;
  workingGraph.cube = fullCube;
  workingGraph.relations = universe.relations;
  RelationUnion rel;
  //std::cout << "Before while" << std::endl;
  while(!pq.empty()) {
    //std::cout << "While start" << std::endl;

    ITGRWorker p = pq.top();
    pq.pop();

    if(p.forwardPhase) {  //Forward Phase
      //std::cout << "F-P" << std::endl;

      Bdd fwd = intersectBdd(p.fwd, universe.nodes); //l7
      ReachResult fwdStep = rel.forwardStep(universe, intersectBdd(universe.nodes, p.front)); //l7
      symbolicSteps += fwdStep.symbolicSteps;
      Bdd front = differenceBdd(fwdStep.set, fwd); //l7
      fwd = unionBdd(fwd, fwdStep.set); //l7

      if(front == leaf_false()) { //If Fixpoint l9
        //move to the next phase
        if(universe.nodes != fwd) {
          ReachResult fwdBasin = rel.backwardSet(universe, fwd);
          Bdd basin = fwdBasin.set;
          symbolicSteps += fwdBasin.symbolicSteps;
          universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, fwd));
        }
        Bdd component = intersectBdd(fireSets[p.index], universe.nodes); //l13
        long long newWeight = component.SatCount(fullCube); //l14
        ITGRWorker newP = {
          newWeight,
          false, //l15
          fwd, //FWD
          component, //Component
          component, //Front
          p.index
        };
        pq.push(newP);
      } else {
        //make another forward step
        long long newWeight = fwd.SatCount(fullCube); //l8
        ITGRWorker newP = { //Update the front and the FWD and the new weight
          newWeight,
          true,
          fwd, 
          p.component,
          front,
          p.index
        };
        pq.push(newP);
      }
    } else { //ExtendedComponent Phase
      workingGraph.nodes = intersectBdd(p.fwd, universe.nodes);
      //workingGraph.nodes = p.fwd;
      workingGraph.relations = universe.relations;

      Bdd extendedComponent = intersectBdd(p.component, universe.nodes);
      ReachResult bwdStep = rel.backwardStep(workingGraph, intersectBdd(universe.nodes, p.front));
      symbolicSteps += bwdStep.symbolicSteps;
      Bdd front = differenceBdd(bwdStep.set, extendedComponent);
      extendedComponent = unionBdd(extendedComponent, bwdStep.set);

      if(front == leaf_false()) {
        //all done now
        Bdd bottom = differenceBdd(intersectBdd(p.fwd, universe.nodes), extendedComponent);
        if(bottom != leaf_false()) {
          ReachResult bottomBasin = rel.backwardSet(universe, bottom);
          Bdd basin = bottomBasin.set;
          symbolicSteps += bottomBasin.symbolicSteps;
          universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, bottom));
        }
        int i = p.index;
        if(intersectBdd(fireSets[i], universe.nodes) == leaf_false()){
          int noDeletions = 0;
          for(int j = 0; j < i; j++) {
            noDeletions += removed[j];
          }
          universe.relations.erase(universe.relations.begin()+i-noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
          removed[i] = true;
        }
        
      } else {
        //take another backward step
        long long newWeight = extendedComponent.SatCount(fullCube);
        ITGRWorker newP = {
          newWeight,
          false,
          p.fwd,
          extendedComponent,
          front,
          p.index
        };
        pq.push(newP);
      }
    }
  }
  std::cout << "Returning universe with " << universe.relations.size() << " relations left" << std::endl;
  std::cout << "And " << universe.nodes.SatCount(universe.cube) << " nodes left " << std::endl;

  return {universe, symbolicSteps};
}