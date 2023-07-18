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
  chain,
  xbSatBottom,
  xbRelUnionBottom,
  chainBottomAdvanced,
  chainBottomSingleRec,
  chainBottomSingleRecSpecialFWD,
  chainBottomSpecialFWD,
  chainBottomForwardLoop,
  chainBottomSingleRecForwardLoop,
  chainBottomSingleRecCumulative,
  chainBottomSingleRecExtra,
  chainBottomSingleRecSwitch,
  chainBottomSingleRecSwitchAndBasin,
  chainBottomApproxPick,
  xbBottomApproxPick,
  chainBottomSingleRecInitState,
  xbBottomInitState
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
    case xbSatBottom:
      return "Xie-Beerel saturation bottom";
    case xbRelUnionBottom:
      return "Xie-Beerel relation union bottom";
    case chainBottomAdvanced:
      return "Chain bottom advanced";
    case chainBottomSingleRec:
      return "Chain bottom single recursion";
    case chainBottomSingleRecSpecialFWD:
      return "Chain bottom single recursion special FWD";
    case chainBottomSpecialFWD:
      return "Chain bottom special FWD";
    case chainBottomForwardLoop:
      return "Chain bottom forward loop";
    case chainBottomSingleRecForwardLoop:
      return "Chain bottom single rec forward loop";
    case chainBottomSingleRecCumulative:
      return "Chain bottom single rec cumulative basin";
    case chainBottomSingleRecExtra:
      return "Chain bottom single rec extra info";
    case chainBottomSingleRecSwitch:
      return "Chain bottom single rec switch";
    case chainBottomSingleRecSwitchAndBasin:
      return "Chain bottom single rec switch and basin";
    case chainBottomApproxPick:
      return "Chain bottom with overapproximations";
    case xbBottomApproxPick:
      return "XB bottom with overapproximations";
    case chainBottomSingleRecInitState:
      return "Chain bottom single rec init state";
    case xbBottomInitState:
      return "Xie-Beerel bottom init state";
    default:
      return "[Unknown algorithm type]";
  }
}

//Timing / benchmark functions
//Main benchmark function
void experiment(std::list<std::string> pathStrings, int minPreprocess, int maxPreprocess,
                bool useInitialMarking, std::list<algorithmType> runTypes, std::string fileName);
//Helper functions
std::vector<std::vector<std::string>> timeAll(const Graph &graph, std::list<algorithmType> runTypes,
                                              std::vector<std::vector<std::string>> grid, int row);
std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> timeRun(const Graph &graph,
                                                                                         algorithmType runType);

//Preprocessing
std::vector<std::vector<std::string>> preprocessAndRun(const Graph &graph, int maxPruning, int minPruning,
                                                       std::list<algorithmType> runTypes,
                                                       std::vector<std::vector<std::string>> grid, int row);
Graph graphPreprocessing(const Graph &graph, int pruningSteps);
Graph graphPreprocessingFixedPoint(const Graph &graph);
std::pair<Graph, int> graphPreprocessingFixedPointWithMax(const Graph &graph, int maxPruning);

//CSV writing functions
void writeToCSV(std::string fileName, std::vector<std::vector<std::string>> grid);
std::vector<std::vector<std::string>> initCsvGrid(int noOfExperimentGraphs, int noOfAlgorithms);

//Functions returning paths to PNML petri nets
std::list<std::string> getPathStringsAll();
std::list<std::string> getPathStringsSlow();
std::list<std::string> getPathStringsBscc();

std::list<std::string> getPintStrings();

//Correctness of results
bool sccListCorrectness(const std::list<sylvan::Bdd> sccList1, const std::list<sylvan::Bdd> sccList2);
bool sccListContainsDifferentSccsWithDuplicateNodes(const std::list<sylvan::Bdd> sccList);
bool sccUnionIsWholeBdd(const std::list<sylvan::Bdd> sccList, const sylvan::Bdd nodes);
bool containsDuplicateSccs(const std::list<sylvan::Bdd> sccList);
void validateAlgoSccResults(const std::list<sylvan::Bdd> resultSccList, const Graph originalGraph);

//Relation analysis
void analyzeRelations(std::deque<Relation> relations);
void printVectorGrid(std::vector<std::vector<bool>> grid);
void analyzeAllRelations(std::list<std::string> pnmlList);

#endif //BENCHMARK_H