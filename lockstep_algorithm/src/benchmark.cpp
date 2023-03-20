#include <filesystem>
#include <list>
#include <string>
#include <deque>
#include <iostream>
#include <deque>
#include <algorithm>
#include <chrono>
#include <vector>
#include <fstream>
#include <math.h>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "benchmark.h"
#include "scc.h"
#include "petriTranslation.h"
#include "bdd_utilities.h"
#include "graph_creation.h"
#include "print.h"
#include "../test/graph_examples.h"
#include "bscc.h"

std::list<std::string> getPathStringsBscc() {
  std::list<std::string> resultList = {};

  // < 15 minutes
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_a_17place.pnml");        //1 BSCCs / 16 SCCs
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_a_24place.pnml");      //16 BSCCs / 368 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_a_31place.pnml");        //8 BSCCs / 2362 SCCs
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_a_34place.pnml");      //3 BSCCs / 406 SCCs
  resultList.push_back("SmartHome/PT/smhome_01_38place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_a_40place.pnml");      //256 BSCCs / 118208 SCCs
  resultList.push_back("SmartHome/PT/smhome_02_41place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_b_43place.pnml");        //1 BSCCs / 479 SCCs
  resultList.push_back("SmartHome/PT/smhome_03_45place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_a_45place.pnml");        //51 BSCCs / 327762 SCCs
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_b_53place.pnml");        //1 BSCCs / 2909 SCCs
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_b_71place.pnml");      //3 BSCCs / 123725 SCCs
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_b_73place.pnml");      //1 BSCCs / 170860 SCCs
  resultList.push_back("SmartHome/PT/smhome_04_139place.pnml");               //8 BSCCs / 10126 SCCs


  // Feasible bsccs of the larger ones *These are also in the list below*
  resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56 - 90s // 4096 BSCCs
  
  
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59 - 4 min // ??
  // resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81 - 30s // 3 BSCCs
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83 - 30s // 8 BSCCs
  // //resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103 - 100s //146 BSCCs
  // resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112 - 15s //??
  // resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117 - 8s //15 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119 - 15s //27 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121 - 25s //51 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123 - 30s //99 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125 - 40s //195 BSCCs
  // resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133 - 2s //1 BSCCs


  // > 15 minutes - not checked yet for only 1 SCC
  //resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56 - 90s
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59 - 4 min
  //resultList.push_back("DiscoveryGPU/PT/discovery_06_a_63place.pnml");                        //63 - 1 SCC
  //resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_a_65place.pnml");                      //65 - slow
  //resultList.push_back("GPUForwardProgress/PT/gpufp_16_a_72place.pnml");                      //72 - slow
  //resultList.push_back("DiscoveryGPU/PT/discovery_07_a_73place.pnml");                        //73 - 1 SCC
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_005_a_73place.pnml");                        //73 - slow
  //resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81 - 30s
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83 - 30s
  //resultList.push_back("DiscoveryGPU/PT/discovery_08_a_83place.pnml");                        //83 - 1 SCC
  //resultList.push_back("GPUForwardProgress/PT/gpufp_20_a_88place.pnml");                      //88 - slow
  //resultList.push_back("DiscoveryGPU/PT/discovery_09_a_93place.pnml");                        //93 - 1 SCC
  //resultList.push_back("ShieldPPPs/PT/shield_s_ppp_003_a_96place.pnml");                      //96 - slow
  //resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103 - 100s
  //resultList.push_back("DiscoveryGPU/PT/discovery_10_a_103place.pnml");                       //103 - 1 SCC
  // resultList.push_back("GPUForwardProgress/PT/gpufp_24_a_104place.pnml");                     //104 - slow
  // resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112 - 15s
  // resultList.push_back("DiscoveryGPU/PT/discovery_11_a_113place.pnml");                       //113 - 1 SCC
  // resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117 - 8s
  // resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119 - 15s
  // resultList.push_back("GPUForwardProgress/PT/gpufp_28_a_120place.pnml");                     //120 - slow
  // resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121 - 25s
  // resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123 - 30s
  // resultList.push_back("DiscoveryGPU/PT/discovery_12_a_123place.pnml");                       //123 - 1 SCC
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_003_b_123place.pnml");                       //123 - slow
  // resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125 - 40s
  // resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133 - 2s
  // resultList.push_back("GPUForwardProgress/PT/gpufp_32_a_136place.pnml");                     //136 - slow
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_b_139place.pnml");                     //139 - slow*/
  // resultList.push_back("DiscoveryGPU/PT/discovery_14_a_143place.pnml");                       //143
  // resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_b_143place.pnml");                     //143
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_010_a_143place.pnml");                       //143
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_004_a_127place.pnml");                     //127
  // resultList.push_back("GPUForwardProgress/PT/gpufp_36_a_152place.pnml");                     //152
  // resultList.push_back("ShieldRVt/PT/shield_t_rv_003_b_153place.pnml");                       //153
  // resultList.push_back("DiscoveryGPU/PT/discovery_15_a_153place.pnml");                       //153
  // resultList.push_back("HealthRecord/PT/hrec_06_154place.pnml");                              //154
  // resultList.push_back("HealthRecord/PT/hrec_07_155place.pnml");                              //155
  // resultList.push_back("HealthRecord/PT/hrec_08_156place.pnml");                              //156
  // resultList.push_back("HealthRecord/PT/hrec_09_157place.pnml");                              //157
  // resultList.push_back("HealthRecord/PT/hrec_10_158place.pnml");                              //158
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_005_a_158place.pnml");                     //158
  // resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_b_159place.pnml");                     //159
  // resultList.push_back("HealthRecord/PT/hrec_11_159place.pnml");                              //159
  // resultList.push_back("HealthRecord/PT/hrec_12_160place.pnml");                              //160
  // resultList.push_back("HealthRecord/PT/hrec_13_161place.pnml");                              //161
  // resultList.push_back("HealthRecord/PT/hrec_14_162place.pnml");                              //162
  // resultList.push_back("HealthRecord/PT/hrec_15_163place.pnml");                              //163
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_004_b_163place.pnml");                       //163
  // resultList.push_back("GPUForwardProgress/PT/gpufp_40_a_168place.pnml");                     //168
  // resultList.push_back("DiscoveryGPU/PT/discovery_06_b_184place.pnml");                       //184
  // resultList.push_back("GPUForwardProgress/PT/gpufp_08_b_188place.pnml");                     //188
  // resultList.push_back("ShieldRVt/PT/shield_t_rv_004_b_203place.pnml");                       //203
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_005_b_203place.pnml");                       //203
  // resultList.push_back("DiscoveryGPU/PT/discovery_07_b_212place.pnml");                       //212
  // resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_b_213place.pnml");                     //213

  return resultList;
}

//These pathstrings were sorted with HumanSort *TM*
std::list<std::string> getPathStringsAll() {
  std::list<std::string> resultList = {};

  // < 15 minutes
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_a_11place.pnml");                        //11
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_a_17place.pnml");                        //17
  resultList.push_back("ShieldRVt/PT/shield_t_rv_002_a_19place.pnml");                        //19
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_a_22place.pnml");                      //22
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_a_24place.pnml");                      //24
  resultList.push_back("ShieldRVt/PT/shield_t_rv_003_a_27place.pnml");                        //27
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_a_28place.pnml");                      //28
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_a_31place.pnml");                        //31
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_a_34place.pnml");                      //34
  resultList.push_back("ShieldRVt/PT/shield_t_rv_004_a_35place.pnml");                        //35
  resultList.push_back("SmartHome/PT/smhome_01_38place.pnml");                                //38
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_a_40place.pnml");                      //40
  resultList.push_back("SmartHome/PT/smhome_02_41place.pnml");                                //41
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_a_41place.pnml");                      //41
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_b_43place.pnml");                        //43
  resultList.push_back("ShieldRVt/PT/shield_t_rv_005_a_43place.pnml");                        //43
  resultList.push_back("SmartHome/PT/smhome_03_45place.pnml");                                //45
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_a_45place.pnml");                        //45
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_b_53place.pnml");                        //53
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_a_53place.pnml");                      //53
  /*resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_a_60place.pnml");                      //60
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_b_71place.pnml");                      //71
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_b_73place.pnml");                      //73
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_003_a_78place.pnml");                      //78
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_004_a_79place.pnml");                      //79
  resultList.push_back("ShieldRVt/PT/shield_t_rv_010_a_83place.pnml");                        //83
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_005_a_98place.pnml");                      //98
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_004_a_103place.pnml");                     //103
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_005_a_128place.pnml");                     //128
  resultList.push_back("SmartHome/PT/smhome_04_139place.pnml");                               //139
  resultList.push_back("ShieldRVt/PT/shield_t_rv_020_a_163place.pnml");                       //163
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_010_a_193place.pnml");                     //193
*/
  return resultList;
}

std::list<std::string> getPathStringsSlow() {
  std::list<std::string> resultList = {};

  // > 15 minutes
  resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56
  resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59
  resultList.push_back("DiscoveryGPU/PT/discovery_06_a_63place.pnml");                        //63
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_a_65place.pnml");                      //65
  resultList.push_back("GPUForwardProgress/PT/gpufp_16_a_72place.pnml");                      //72
  resultList.push_back("DiscoveryGPU/PT/discovery_07_a_73place.pnml");                        //73
  resultList.push_back("ShieldRVs/PT/shield_s_rv_005_a_73place.pnml");                        //73
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83
  resultList.push_back("DiscoveryGPU/PT/discovery_08_a_83place.pnml");                        //83
  resultList.push_back("GPUForwardProgress/PT/gpufp_20_a_88place.pnml");                      //88
  resultList.push_back("DiscoveryGPU/PT/discovery_09_a_93place.pnml");                        //93
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_003_a_96place.pnml");                      //96
  resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103
  resultList.push_back("DiscoveryGPU/PT/discovery_10_a_103place.pnml");                       //103
  resultList.push_back("GPUForwardProgress/PT/gpufp_24_a_104place.pnml");                     //104
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112
  resultList.push_back("DiscoveryGPU/PT/discovery_11_a_113place.pnml");                       //113
  resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117
  resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119
  resultList.push_back("GPUForwardProgress/PT/gpufp_28_a_120place.pnml");                     //120
  resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121
  resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123
  resultList.push_back("DiscoveryGPU/PT/discovery_12_a_123place.pnml");                       //123
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_b_123place.pnml");                       //123
  resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125
  resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133
  resultList.push_back("GPUForwardProgress/PT/gpufp_32_a_136place.pnml");                     //136
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_b_139place.pnml");                     //139
  resultList.push_back("DiscoveryGPU/PT/discovery_14_a_143place.pnml");                       //143
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_b_143place.pnml");                     //143
  resultList.push_back("ShieldRVs/PT/shield_s_rv_010_a_143place.pnml");                       //143
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_004_a_127place.pnml");                     //127
  resultList.push_back("GPUForwardProgress/PT/gpufp_36_a_152place.pnml");                     //152
  resultList.push_back("ShieldRVt/PT/shield_t_rv_003_b_153place.pnml");                       //153
  resultList.push_back("DiscoveryGPU/PT/discovery_15_a_153place.pnml");                       //153
  resultList.push_back("HealthRecord/PT/hrec_06_154place.pnml");                              //154
  resultList.push_back("HealthRecord/PT/hrec_07_155place.pnml");                              //155
  resultList.push_back("HealthRecord/PT/hrec_08_156place.pnml");                              //156
  resultList.push_back("HealthRecord/PT/hrec_09_157place.pnml");                              //157
  resultList.push_back("HealthRecord/PT/hrec_10_158place.pnml");                              //158
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_005_a_158place.pnml");                     //158
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_b_159place.pnml");                     //159
  resultList.push_back("HealthRecord/PT/hrec_11_159place.pnml");                              //159
  resultList.push_back("HealthRecord/PT/hrec_12_160place.pnml");                              //160
  resultList.push_back("HealthRecord/PT/hrec_13_161place.pnml");                              //161
  resultList.push_back("HealthRecord/PT/hrec_14_162place.pnml");                              //162
  resultList.push_back("HealthRecord/PT/hrec_15_163place.pnml");                              //163
  resultList.push_back("ShieldRVs/PT/shield_s_rv_004_b_163place.pnml");                       //163
  resultList.push_back("GPUForwardProgress/PT/gpufp_40_a_168place.pnml");                     //168
  resultList.push_back("DiscoveryGPU/PT/discovery_06_b_184place.pnml");                       //184
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_b_188place.pnml");                     //188
  resultList.push_back("ShieldRVt/PT/shield_t_rv_004_b_203place.pnml");                       //203
  resultList.push_back("ShieldRVs/PT/shield_s_rv_005_b_203place.pnml");                       //203
  resultList.push_back("DiscoveryGPU/PT/discovery_07_b_212place.pnml");                       //212
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_b_213place.pnml");                     //213

  // XB worst-case graphs
  //resultList.push_back("xb_slow100.pnml");
  //resultList.push_back("xb_slow200.pnml");
  /*resultList.push_back("xb_slow300.pnml");
  resultList.push_back("xb_slow400.pnml");
  resultList.push_back("xb_slow500.pnml");
  resultList.push_back("xb_slow600.pnml");*/

  return resultList;
}

//Main experimentation function
//Runs each algorithm on a list of graphs from PNML files with varying preprocessing amounts
//Prints the results and writes them to a csv-file
void experiment(std::list<std::string> pathStrings, int minPreprocess, int maxPreprocess,
                bool useInitialMarking, std::list<algorithmType> runTypes, std::string fileName) {
  //The amount of files and algorithms to run experiments on - is used to init the size of the csv-file rows
  int noFiles = pathStrings.size();
  int noAlgorithms = runTypes.size();

  //CSV filename and empty container for the rows and init row 0 headers
  std::vector<std::vector<std::string>> grid = initCsvGrid(noFiles, noAlgorithms);
  //The current csv row to insert results into
  int csvRow = 0;

  //Read all the files, create their graphs and run the algorithms on them
  for(std::string pathString : pathStrings) {
    std::cout << "###### Running experiment on file at path: " << pathString << std::endl;
    //Create the graph from the PNML-file
    Graph graph = PNMLtoGraph(pathString, useInitialMarking);

    //Write number of places and relations to csv-file
    std::string noOfPlaces = std::to_string(graph.cube.size());
    std::string noOfRelations = std::to_string(graph.relations.size());
    int i = 1;
    for(algorithmType algo : runTypes) {
      grid[csvRow+i].insert(grid[csvRow+i].end(), {algoToString(algo), noOfPlaces, noOfRelations});
      i++;
    }

    grid = preprocessAndRun(graph, maxPreprocess, minPreprocess, runTypes, grid, csvRow);

    //Move down in the csv grid to make way for the next run
    csvRow = csvRow+noAlgorithms+2;
  }
  writeToCSV(fileName, grid);
}

//Run all algorithms with all pruning steps that are powers of 2 between max and min
//maxPruning < 0 means fixed-point pruning
std::vector<std::vector<std::string>> preprocessAndRun(const Graph &graph, int maxPruning, int minPruning,
                                                       std::list<algorithmType> runTypes,
                                                       std::vector<std::vector<std::string>> grid, int row) {
  if(minPruning < 0) {
    minPruning = 0;
  }
  if(maxPruning < minPruning) {
    minPruning = maxPruning;
  }
  if(maxPruning < 0) {
    std::cout << "### With pre-processing (fixed point)" << std::endl;
    Graph processedGraph = graphPreprocessingFixedPoint(graph);


    std::cout << "Counting with SatCount..:" << std::endl;
    double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
    std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

    std::string nodeCountString =  std::to_string(nodeCount);
    std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

    for(int i = 1 ; i <= runTypes.size() ; i++) {
      grid[row+i].push_back(nodeCountString);
    }

    grid = timeAll(processedGraph, runTypes, grid, row);
    std::cout << std::endl;

    grid[row].insert(grid[row].end(), {"Nodes" , "SCCs", "Running time (ms)", "SSCs/ms", "Symbolic steps"});
  }
  else {
    if(maxPruning == 0) {
      std::cout << "### With no pre-processing" << std::endl;
      Graph processedGraph = graphPreprocessing(graph, 0);

      std::cout << "Counting with SatCount..:" << std::endl;
      double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
      std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

      std::string nodeCountString =  std::to_string(nodeCount);
      std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

      for(int i = 1 ; i <= runTypes.size() ; i++) {
        grid[row+i].push_back(nodeCountString);
      }

      grid = timeAll(graph, runTypes, grid, row);
      grid[row].insert(grid[row].end(), {"Nodes", "SCC's", std::to_string(0) + " pruning steps (ms)", "SCC/ms", "Symbolic steps" });
    }
    else {
      std::cout << "### With pre-processing (" << std::to_string(maxPruning) << " or fixed-point)" << std::endl;
      std::pair<Graph, int> result = graphPreprocessingFixedPointWithMax(graph, maxPruning);
      Graph processedGraph = result.first;

      std::cout << "Counting with SatCount..:" << std::endl;
      double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
      std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

      std::string nodeCountString =  std::to_string(nodeCount);
      std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

      for(int i = 1 ; i <= runTypes.size() ; i++) {
        grid[row+i].push_back(nodeCountString);
      }

      int newMax = result.second;
      int newMax2Pow = pow(2,floor(log2(newMax-1)));

      grid = timeAll(processedGraph, runTypes, grid, row);
      std::cout << std::endl;
      grid[row].insert(grid[row].end(), {"Nodes", "SCC's", std::to_string(newMax) + " pruning steps (ms)", "SCC/ms", "Symbolic steps" });

      for(int i = newMax2Pow; i >= minPruning; i = floor(i/2)) {
        std::cout << "### With pre-processing (" << std::to_string(i) << ")" << std::endl;
        processedGraph = graphPreprocessing(graph, i);

        std::cout << "Counting with SatCount..:" << std::endl;
        double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
        std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

        std::string nodeCountString =  std::to_string(nodeCount);
        std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

        for(int i = 1 ; i <= runTypes.size() ; i++) {
          grid[row+i].push_back(nodeCountString);
        }

        grid = timeAll(processedGraph, runTypes, grid, row);
        std::cout << std::endl;

        grid[row].insert(grid[row].end(), {"Nodes", "SCC's", std::to_string(i) + " pruning steps (ms)", "SCC/ms", "Symbolic steps" });

        if(i == 0 || i == minPruning) {
          break;
        }
      }
    }
  }
  return grid;
}

//Finds SCCs on a graph with each algorithm, and appends them to the CSV-grid which is returned
std::vector<std::vector<std::string>> timeAll(const Graph &graph, std::list<algorithmType> runTypes, std::vector<std::vector<std::string>> grid, int row) {
  int i = 1;
  for(algorithmType runType : runTypes) {
    std::cout << "Running algorithm: " << algoToString(runType) << std::endl;
    std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> runResults = timeRun(graph, runType);
    std::list<sylvan::Bdd> sccList = std::get<0>(runResults);
    std::chrono::duration<long, std::milli> duration = std::get<1>(runResults);

    std::string annoyingFloatString =  std::to_string((float)sccList.size() / duration.count());
    std::replace(annoyingFloatString.begin(), annoyingFloatString.end(), '.', ',');
    grid[row+i].insert(grid[row+i].end(), {std::to_string(sccList.size()), std::to_string(duration.count()), annoyingFloatString, std::to_string(std::get<2>(runResults))});

    i++;
  }
  return grid;
}

//Runs the specified algorithm on the graph and returns how long it took and the number of symbolic steps
//Also prints timing and results
std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> timeRun(const Graph &graph, algorithmType runType) {
  SccResult sccAndSteps;
  std::list<sylvan::Bdd> sccList;
  int steps = 0;
  auto start = std::chrono::high_resolution_clock::now();
  switch(runType) {
    case lockstepSat:
      sccAndSteps = lockstepSaturation(graph);
      break;
    case lockstepRelUnion:
      sccAndSteps = lockstepRelationUnion(graph);
      break;
    case xbSat:
      sccAndSteps = xieBeerel<Saturation>(graph);
      break;
    case xbRelUnion:
      sccAndSteps = xieBeerel<RelationUnion>(graph);
      break;
    case skeleton:
      sccAndSteps = skeletonAlg(graph);
      break;
    case chain:
      sccAndSteps = chainAlg(graph);
      break;
    case xbRelUnionBottom:
      sccAndSteps = xieBeerelBottom<RelationUnion>(graph);
      break;
    case xbSatBottom:
      sccAndSteps = xieBeerelBottom<Saturation>(graph);
      break;
    case chainBottomAdvanced:
      sccAndSteps = chainAlgBottomAdvanced(graph);
      break;
    case chainBottomSpecialFWD:
      sccAndSteps = chainAlgBottomSpecialFWD(graph);
      break;
    case chainBottomSingleRec:
      sccAndSteps = chainAlgBottomSingleRecCall(graph);
      break;
    case chainBottomSingleRecSpecialFWD:
      sccAndSteps = chainAlgBottomSingleRecSpecialFWD(graph);
      break;
    case chainBottomSingleRecForwardLoop:
      sccAndSteps = chainAlgBottomSingleRecForwardLoop(graph);
      break;
    case chainBottomForwardLoop:
      sccAndSteps = chainAlgBottomForwardLoop(graph);
      break;
    case chainBottomSingleRecCumulative:
      sccAndSteps = chainAlgBottomSingleRecCallCumulative(graph);
      break;
    case chainBottomSingleRecExtra:
      sccAndSteps = chainAlgBottomSingleRecCallExtra(graph);
      break;
    case chainBottomSingleRecSwitch:
      sccAndSteps = chainAlgBottomSingleRecCallSwitch(graph);
      break;
    case chainBottomSingleRecSwitchAndBasin:
      sccAndSteps = chainAlgBottomSingleRecCallSwitchAndBasin(graph);
      break;
    case chainBottomApproxPick:
      sccAndSteps = chainAlgBottomApproxPick(graph);
      break;
    case xbBottomApproxPick:
      sccAndSteps = xbAlgBottomApproxPick(graph);
      break;
  }

  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
  sccList = sccAndSteps.sccs;
  steps = sccAndSteps.symbolicSteps;
  std::cout << "Time elapsed (" << algoToString(runType) << "): " << duration.count() << " milliseconds" << std::endl;
  std::cout << "Found " << sccList.size() << " SCCs" << std::endl << std::endl;
  std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> result = {sccList, duration, steps};
  return result;
}

////////////////////////////////////////////////////////////////////////////////
// CSV
////////////////////////////////////////////////////////////////////////////////


//Writes the grid to a file at fileName.csv
void writeToCSV(std::string fileName, std::vector<std::vector<std::string>> grid) {
  std::ofstream myFile;
  std::string csvFile = fileName + ".csv";
  myFile.open(csvFile);

  //Takes semi-colon separated cells row by row and writes to .csv file
  for(std::vector<std::string> row : grid) {
    for(std::string cell : row) {
      myFile << cell + ";";
    }
    myFile << "\n";

  }
  myFile.close();
}

//Initializes an empty csv grid with the appropriate amount of rows to insert into
std::vector<std::vector<std::string>> initCsvGrid(int noOfExperimentGraphs, int noOfAlgorithms) {
  int noOfRows = (noOfExperimentGraphs) * (noOfAlgorithms+2);

  std::vector<std::vector<std::string>> grid(noOfRows, std::vector<std::string>(0));

  for(int i = 0; i < noOfRows; i = i+noOfAlgorithms+2) {
    grid[i].insert(grid[i].end(), {"Algorithm run", "Places", "Relations"});
  }
  return grid;
}

////////////////////////////////////////////////////////////////////////////////
//Pre-processing
////////////////////////////////////////////////////////////////////////////////

//Sorts the relations by their top and prunes the graph pruningSteps times
Graph graphPreprocessing(const Graph &graph, int pruningSteps) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  for(int i = 0; i < pruningSteps; i++) {
    resultGraph = pruneGraph(resultGraph);
  }

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
  std::cout << "Finished pre-processing of graph" << std::endl;
  return resultGraph;
}

//Sorts the relations by their top and prunes the graph until it has no more 1-node SCCs
Graph graphPreprocessingFixedPoint(const Graph &graph) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  resultGraph = fixedPointPruning(resultGraph);

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
  std::cout << "Finished pre-processing of graph" << std::endl;
  return resultGraph;
}

//Sorts the relations by their top and prunes the graph until it has no more 1-node SCCs or
//it has used the maximum number of pruning steps
std::pair<Graph, int> graphPreprocessingFixedPointWithMax(const Graph &graph, int maxPruning) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  std::pair<Graph, int> result = fixedPointPruningWithMax(resultGraph, maxPruning);

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
  std::cout << "Finished pre-processing of graph" << std::endl;
  return result;
}

////////////////////////////////////////////////////////////////////////////////
//SCC list verification
////////////////////////////////////////////////////////////////////////////////
//For an SCC-list, check that it does not have duplicates, that no SCCs overlap,
//and that it covers the entire original graph
void validateAlgoSccResults(const std::list<sylvan::Bdd> resultSccList, const Graph originalGraph) {
  bool hasDuplicates = containsDuplicateSccs(resultSccList);
  if(hasDuplicates) {
    std::cout << "Lockstep saturation gave two or more equal SCCs" << std::endl;
  }
  bool hasOverlap = sccListContainsDifferentSccsWithDuplicateNodes(resultSccList);
  if(hasOverlap) {
    std::cout << "Lockstep saturation gave overlapping SCCs" << std::endl;
  }
  bool foundAllSCCs = sccUnionIsWholeBdd(resultSccList, originalGraph.nodes);
  if(!foundAllSCCs) {
    std::cout << "Lockstep saturation did not find SCCs covering all nodes" << std::endl;
  }
}

//Finds whether an SCC is contained in a list of SCCs
bool sccListContains(sylvan::Bdd target, std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc : sccList) {
    if(scc == target) {
      return true;
    }
  }
  return false;
}

//Checks for duplicates in a list of SCCs
bool containsDuplicateSccs(const std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc1 : sccList) {
    int duplicates = 0;
    for(sylvan::Bdd scc2 : sccList) {
      if(scc1 == scc2) {
        duplicates++;
      }
    }
    if(duplicates > 1) {
      return true;
    }
  }
  return false;
}

//Checks that no SCCs in an SCC list overlap
bool sccListContainsDifferentSccsWithDuplicateNodes(const std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc1 : sccList) {
    for(sylvan::Bdd scc2 : sccList) {
      sylvan::Bdd intersect = intersectBdd(scc1, scc2);
      if(intersect != leaf_false() && scc1 != scc2) {
        return true;
      }
    }
  }
  return false;
}

//Checks that an SCC list covers a whole nodeset
bool sccUnionIsWholeBdd(const std::list<sylvan::Bdd> sccList, const sylvan::Bdd nodes) {
  sylvan::Bdd bddUnion = leaf_false();
  for(sylvan::Bdd scc : sccList) {
    bddUnion = unionBdd(bddUnion, scc);
  }
  sylvan::Bdd result = differenceBdd(nodes, bddUnion);
  return result == leaf_false();
}

//Checks that two SCC lists contain the same SCCs
bool sccListCorrectness(const std::list<sylvan::Bdd> sccList1, const std::list<sylvan::Bdd> sccList2) {
  if(sccList1.size() != sccList2.size()) {
    std::cout << "The size of the scc lists were different" << std::endl;
    return false;
  }
  if(containsDuplicateSccs(sccList1) || containsDuplicateSccs(sccList2)) {
    std::cout << "One of the lists contained duplicate sccs" << std::endl;
    return false;
  }
  for(sylvan::Bdd scc : sccList1) {
    if(!sccListContains(scc, sccList2)) {
      std::cout << "The lists didn't contain the same scc" << std::endl;
      return false;
    }
  }
  return true;
}

void analyzeRelations(std::deque<Relation> relations) {
  std::list<std::list<bool>> matrix = {};

  std::vector<std::vector<bool>> grid(relations.size(), std::vector<bool>(relations.size()));
  for (int i = 0; i < relations.size(); i++) {
      for (int j = 0; j < relations.size(); j++) {
          Relation relationi = relations[i];
          Relation relationj = relations[j];
          if(i == j) {
              grid[i][j] = false;
              continue;
            }
          //Top is smallest variable and bottom is largest
          if((relationi.bottom >= relationj.top && relationi.bottom <= relationj.bottom)
              || (relationi.top >= relationj.top && relationi.top <= relationj.bottom)
              || (relationj.top >= relationi.top && relationj.top <= relationi.bottom)
              || (relationj.bottom >= relationi.top && relationj.bottom <= relationi.bottom)) {
            grid[i][j] = true;
          } else {
            grid[i][j] = false;
          }
      }
  }
  //calculate average out-degree:
  double matrixsum = 0;
  for (int i = 0; i < relations.size(); i++) {
    for (int j = 0; j < relations.size(); j++) {
      matrixsum += grid[i][j];
    }
  }
  double avgMatrixSum = matrixsum / relations.size();
  double normOutDegree = avgMatrixSum / relations.size();
  double normEdges = avgMatrixSum / 2;
  double density = matrixsum / (relations.size() * (relations.size()-1));
  //printVectorGrid(grid);
  std::cout << "Normalized out-degree: " << normOutDegree << std::endl;
  std::cout << "Normalized number of edges: " << normEdges << std::endl;
  std::cout << "|V|: " << relations.size() << std::endl;
  std::cout << "|E|: " << matrixsum/2 << std::endl;
  std::cout << "Density: " << density << std::endl;
}

void printVectorGrid(std::vector<std::vector<bool>> grid){
  for(std::vector<bool> vec : grid) {
    for(bool b : vec) {
      if(b) {
        std::cout << " 1";
      } else  {
        std::cout << " 0";
      }
    }
    std::cout<< std::endl;
  }
}

void analyzeAllRelations(std::list<std::string> pnmlList) {
  for(std::string pnml : pnmlList ){
    Graph graph = PNMLtoGraph(pnml, true);
    analyzeRelations(graph.relations);
    std::cout << std::endl;
  }
}