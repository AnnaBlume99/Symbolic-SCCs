#ifndef BENCHMARK_H
#define BENCHMARK_H

#include <chrono>

#include "petriTranslation.h"

//Enums for all the runnable functions
enum algorithmType
{
  lockstepSat,
  lockstepRelUnion,
  xbSat,
  xbRelUnion,
  skeleton,
  chain
};

//ToString on the runnable function enums
inline const std::string algoToString(algorithmType runType) {
  switch (runType)
  {
    case lockstepSat:
      return "Lockstep saturation";
    case lockstepRelUnion:
      return "Lockstep relation union";
    case xbSat:
      return "Xie-Beerel saturation";
    case xbRelUnion:
      return "Xie-Beerel relation union";
    case skeleton:
      return "Skeleton";
    case chain:
      return "Chain";
    default:
      return "[Unknown algorithm type]";
  }
}

//Timing / benchmark functions
//Main benchmark function
void experiment(std::list<std::string> pathStrings, algorithmType runType, std::string fileName);

//Helper functions
std::vector<std::vector<std::string>> timeAll(const Graph &graph, algorithmType runType,
                                              std::vector<std::vector<std::string>> grid, int row);
std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> timeRun(const Graph &graph,
                                                                                         algorithmType runType);
std::vector<std::vector<std::string>> run(const Graph &graph,
                                          algorithmType runTypes,
                                          std::vector<std::vector<std::string>> grid, int row);

//CSV writing functions
void writeToCSV(std::string fileName, std::vector<std::vector<std::string>> grid);
std::vector<std::vector<std::string>> initCsvGrid(int noOfExperimentGraphs);

//Functions returning paths to PNML petri nets
std::list<std::string> getPathStringsFast();
std::list<std::string> getPathStringsSlow();

#endif //BENCHMARK_H