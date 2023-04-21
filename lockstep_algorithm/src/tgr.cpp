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
      universe.relations.erase(universe.relations.begin()+i- noDeletions); //This might be inefficent, however does not affect the symbolic steps we are interested in
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


