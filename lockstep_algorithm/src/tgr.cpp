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
  Bdd reach;
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
      fireSet,
      leaf_false(),
      fireSet,
      i
    };
    pq.push(worker);
  }

  /*while(!pq.empty()) {
    ITGRWorker p = pq.top();
    pq.pop();

    std::cout << p.weight << std:: endl;
  }
  std::exit(-1);*/

  RelationUnion rel;
  //std::cout << "Before while" << std::endl;
  while(!pq.empty()) {
    //std::cout << "While start" << std::endl;

    ITGRWorker p = pq.top();
    pq.pop();

    if(p.forwardPhase) { //Forward Phase
      //std::cout << "F-P" << std::endl;

      Bdd newReach = intersectBdd(p.reach, universe.nodes);
      ReachResult fwdStep = rel.forwardStep(universe, intersectBdd(universe.nodes, p.front));
      symbolicSteps += fwdStep.symbolicSteps;
      newReach = unionBdd(newReach, fwdStep.set);

      if(differenceBdd(fwdStep.set, newReach) == leaf_false()) { //If Fixpoint
      //std::cout << "F-P 1" << std::endl;
        //move to the next phase
        if(universe.nodes != newReach) {
          ReachResult fwdBasin = rel.backwardSet(universe, newReach);
          Bdd basin = fwdBasin.set;
          symbolicSteps += fwdBasin.symbolicSteps;
          universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, newReach));
        }
        Bdd component = intersectBdd(fireSets[p.index], universe.nodes);
        long long newWeight = component.SatCount(fullCube);
        ITGRWorker newP = {
          newWeight,
          false,
          newReach, //This is FWD
          component,
          component,
          p.index
        };
        pq.push(newP);
      } else {
        std::cout << "F-P 2" << std::endl;
        //make another forward step
        long long newWeight = newReach.SatCount(fullCube);
        ITGRWorker newP = {
          newWeight,
          true,
          newReach,
          p.component,
          fwdStep.set,
          p.index
        };
        pq.push(newP);
      }
    } else { //ExtendedComponent Phase
      //std::cout << "E-P" << std::endl;
      Bdd newComponent = intersectBdd(p.component, universe.nodes);
      ReachResult bwdStep = rel.backwardStep(universe, intersectBdd(universe.nodes, p.front));
      symbolicSteps += bwdStep.symbolicSteps;
      newComponent = unionBdd(newComponent, bwdStep.set);

      if(differenceBdd(bwdStep.set, newComponent) == leaf_false()) {
        //std::cout << "E-P 2" << std::endl;
        //all done now
        Bdd bottom = differenceBdd(intersectBdd(p.reach, universe.nodes), newComponent);
        if(bottom != leaf_false()) {
            ReachResult bottomBasin = rel.backwardSet(universe, bottom);
            Bdd basin = bottomBasin.set;
            symbolicSteps += bottomBasin.symbolicSteps;
            universe.nodes = differenceBdd(universe.nodes, differenceBdd(basin, bottom));
        }

        if(intersectBdd(fireSets[p.index], universe.nodes) == leaf_false()){
          //std::cout << "E-P 2a" << std::endl;
          int i = p.index;
          int noDeletions = 0;
          for(int j = 0; j < i; j++) {
            noDeletions += removed[j];
          }
          //std::cout << "Universe relations size: " << universe.relations.size() << std::endl;
          //std::cout << "Deleting on place " << i - noDeletions << " with " << noDeletions << " deletions" << std::endl;
          universe.relations.erase(universe.relations.begin()+i-noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
          //std::cout << "E-P 2b" << std::endl;
          removed[i] = true;
        }
        
      } else {
        //std::cout << "E-P 3" << std::endl;
        //take another backward step
        long long newWeight = newComponent.SatCount(fullCube);
        ITGRWorker newP = {
          newWeight,
          false,
          p.reach,
          newComponent,
          bwdStep.set,
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