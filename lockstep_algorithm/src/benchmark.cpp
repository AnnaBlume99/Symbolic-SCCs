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

//These pathstrings were sorted with HumanSort *TM*
std::list<std::string> getPathStringsFast() {
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
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_a_60place.pnml");                      //60
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

  return resultList;
}

//Main experimentation function
//Runs each algorithm on a list of graphs from PNML files with varying preprocessing amounts
//Prints the results and writes them to a csv-file
void experiment(std::list<std::string> pathStrings, algorithmType runType, std::string fileName) {
  //The amount of files and algorithms to run experiments on - is used to init the size of the csv-file rows
  int noFiles = pathStrings.size();

  //CSV filename and empty container for the rows and init row 0 headers
  std::vector<std::vector<std::string>> grid = initCsvGrid(noFiles);
  //The current csv row to insert results into
  int csvRow = 0;
  grid[0].insert(grid[0].end(), {"Nodes", "SCCs", "Running time (ms)", "Symbolic steps"});

  //Read all the files, create their graphs and run the algorithms on them
  for(std::string pathString : pathStrings) {
    std::cout << "###### Running experiment on file at path: " << pathString << std::endl;
    //Create the graph from the PNML-file
    Graph graph = PNMLtoGraph(pathString);

    //Write number of places and relations to csv-file
    std::string noOfPlaces = std::to_string(graph.cube.size());
    std::string noOfRelations = std::to_string(graph.relations.size());

    grid[csvRow+1].insert(grid[csvRow+1].end(), {pathString, noOfPlaces, noOfRelations});
    grid = run(graph, runType, grid, csvRow);

    //Move down in the csv grid to make way for running all algorithms on next graph
    csvRow = csvRow+1;
  }

  writeToCSV(fileName, grid);
}

std::vector<std::vector<std::string>> run(const Graph &graph,
                                          algorithmType runType,
                                          std::vector<std::vector<std::string>> grid, int row) {

  long long nodeCount = graph.nodes.SatCount(graph.cube);
  std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

  std::string nodeCountString =  std::to_string(nodeCount);
  std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

  grid[row+1].push_back(nodeCountString);

  grid = timeAll(graph, runType, grid, row);

  return grid;
}

//Finds SCCs on a graph with each algorithm, and appends them to the CSV-grid which is returned
std::vector<std::vector<std::string>> timeAll(const Graph &graph, algorithmType runType, std::vector<std::vector<std::string>> grid, int row) {
  std::cout << "Running algorithm: " << algoToString(runType) << std::endl;
  std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> runResults = timeRun(graph, runType);
  std::list<sylvan::Bdd> sccList = std::get<0>(runResults);
  std::chrono::duration<long, std::milli> duration = std::get<1>(runResults);

  grid[row+1].insert(grid[row+1].end(), {std::to_string(sccList.size()), std::to_string(duration.count()), std::to_string(std::get<2>(runResults))});

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
  }

  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
  sccList = sccAndSteps.sccs;
  steps = sccAndSteps.symbolicSteps;
  std::cout << "Time elapsed (" << algoToString(runType) << "): " << duration.count() << " milliseconds" << std::endl;
  std::cout << "Found " << sccList.size() << " SCCs" << std::endl;
  std::cout << "Used " << steps << " symbolic steps" << std::endl << std::endl;
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
std::vector<std::vector<std::string>> initCsvGrid(int noOfExperimentGraphs) {
  int noOfRows = (noOfExperimentGraphs) + 2;
  std::vector<std::vector<std::string>> grid(noOfRows, std::vector<std::string>(0));
  grid[0].insert(grid[0].end(), {"File", "Places", "Relations"});
  return grid;
}
