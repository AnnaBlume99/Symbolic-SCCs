#include <filesystem>
#include <list>
#include <string>
#include <deque>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "graph_examples.h"
#include "../src/scc.h"
#include "../src/petriTranslation.h"
#include "../src/bdd_utilities.h"
#include "../src/graph_creation.h"

Graph noGraph() {
  std::list<std::pair<int, int>> r1 = {};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(0, relationList);
  return result;
}

Graph oneNodeGraph() {
  std::list<std::pair<int, int>> r1 = {};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(1, relationList);
  return result;
}

Graph oneNodeGraphSelfLoop() {
  std::list<std::pair<int, int>> r1 =
    {{0,0}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(1, relationList);
  return result;
}

Graph twoNodeGraphTwoSCCs() {
  std::list<std::pair<int, int>> r1 =
    {{0,1}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(2, relationList);
  return result;
}

Graph twoNodeGraphOneSCC() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},{1,0}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(2, relationList);
  return result;
}

Graph twoNodeGraphTwoRelations() {
  std::list<std::pair<int, int>> r1 =
    {{0,1}};
  std::list<std::pair<int, int>> r2 =
    {{1,0}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1,r2};
  Graph result = makeGraph(2, relationList);
  return result;
}

Graph fourNodesOneRelation() {
  std::list<std::pair<int, int>> r1 =
    {{0,1}, {0,2}, {1,3}, {3,0}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(4, relationList);
  return result;
}

Graph nonConnectedGraph() {
  std::list<std::pair<int, int>> r1 = {};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(2, relationList);
  return result;
}

Graph graphExample1oneRel() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},{1,0},{0,2},{2,1},{1,3},{2,4},{4,3},{4,5},{4,6},{4,7},{5,6},{6,7},{7,5},{7,8}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(9, relationList);
  return result;
}

#1
Graph graphExample1multRel() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},{1,0},{0,2},{4,5},{4,6},{4,7},{5,6}};
  std::list<std::pair<int, int>> r2 =
    {{2,4},{4,3},{6,7}};
  std::list<std::pair<int, int>> r3 =
    {{2,1},{1,3},{7,5},{7,8}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1,r2,r3};
  Graph result = makeGraph(9, relationList);
  return result;
}

#2
Graph graphExample2oneRel() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},
     {1,2},{2,1},{2,3},
     {3,4},{4,3},{4,5},{5,4},{5,6},
     {6,7},{7,6},{7,8},{8,7},{8,9},{9,8},{9,10},
     {10,11},{11,10},{11,12},{12,11},{12,13},{13,12},{13,14},{14,13},{14,15},
     {15,16},{16,15},{16,17},{17,16},{17,18},{18,17},{18,19},{19,18},{19,20},{20,19}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(21, relationList);
  return result;
}

Graph graphExample2multRel() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},{1,2},{3,4},{6,7},{10,11},{15,16}};
  std::list<std::pair<int, int>> r2 =
    {{2,1},{4,3},{7,6},{11,10},{16,15}};
  std::list<std::pair<int, int>> r3 =
    {{2,3},{4,5},{7,8},{11,12},{16,17}};
  std::list<std::pair<int, int>> r4 =
    {{5,4},{8,7},{12,11},{17,16}};
  std::list<std::pair<int, int>> r5 =
    {{5,6},{8,9},{12,13},{17,18}};
  std::list<std::pair<int, int>> r6 =
    {{9,8},{13,12},{18,17}};
  std::list<std::pair<int, int>> r7 =
    {{9,10},{13,14},{18,19}};
  std::list<std::pair<int, int>> r8 =
    {{14,13},{19,18}};
  std::list<std::pair<int, int>> r9 =
    {{14,15},{19,20},{20,19}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1,r2,r3,r4,r5,r6,r7,r8,r9};
  Graph result = makeGraph(21, relationList);
  return result;
}

#3
Graph graphExample3oneRel() {
  std::list<std::pair<int, int>> r1 =
    {{0,1},{1,2},{2,3},{3,4},{4,0},{1,0},{2,0},{3,0}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1};
  Graph result = makeGraph(5, relationList);
  return result;
}

Graph graphExample3multRel() {
  std::list<std::pair<int, int>> r1 =
    {{1,0},{2,0},{3,0},{4,0}};
  std::list<std::pair<int, int>> r2 =
    {{0,1},{1,2},{2,3},{3,4}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1,r2};
  Graph result = makeGraph(5, relationList);
  return result;
}


Graph graphExampleBscc1oneRel() {

  std::list<std::pair<int, int>> r1 = 
    {{0,1}, {1,0}, {0,2}, {0,3}, {1,4}, {1,5}, {5,6}, {6,5}};
    const std::list<std::list<std::pair<int, int>>> relationList = {r1};
    Graph result = makeGraph(7, relationList);
    return result;
}


Graph graphExampleBscc1multRel() {
  std::list<std::pair<int, int>> r1 = 
    {{0,1}, {1,0}, {0,2}, {0,3}};
  std::list<std::pair<int, int>> r2 = 
    {{1,4}, {1,5}, {5,6}, {6,5}};
  const std::list<std::list<std::pair<int, int>>> relationList = {r1, r2};
  Graph result = makeGraph(7, relationList);
  return result;
}


Graph graphExampleBscc2oneRel() {
  std::list<std::pair<int, int>> r1 = 
    {{2,1}, {2,0}, {2,3}, {1,0}, {1,4}, {1,5}, {0,5}, {0,6}, {3,6}, {3,7}, {3,8}};
    const std::list<std::list<std::pair<int, int>>> relationList = {r1};
    Graph result = makeGraph(9, relationList);
    return result;
}


Graph graphExampleBscc3oneRel(){
  std::list<std::pair<int, int>> r1 = 
    {{2,1}, {2,0}, {2,3}, {1,0}, {1,4}, {1,5}, {0,5}, {0,6}, {3,6}, {3,7}, {3,8}
    ,{11,10}, {11,9}, {11,12}, {10,9}, {10,13}, {10,14}, {9,14}, {9,15}, {12,15}, {12,16}, {12,17}
    ,{18,0}, {18,9}
    };
    const std::list<std::list<std::pair<int, int>>> relationList = {r1};
    Graph result = makeGraph(19, relationList);
    return result;


}


