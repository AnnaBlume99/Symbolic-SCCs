#include <iostream>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "scc.h"
#include "petriTranslation.h"
#include "benchmark.h"
#include "print.h"
#include "interface.h"
#include "../test/graph_examples.h"
#include "../test/test_sccListCorrectness.h"

int main() {

  // Init LACE
  lace_start(1, 10000000);

  const size_t memory_bytes = 1024u * 1024u * 1024u;

  // Init Sylvan
  sylvan::sylvan_set_limits(memory_bytes, // Set memory limit
                            6,            // Set (exponent) of cache ratio
                            0);           // Initialise unique node table to full size
  sylvan::sylvan_set_granularity(1);
  sylvan::sylvan_init_package();
  sylvan::sylvan_init_bdd();

  std::cout << "Hello SCC-finding World!" << std::endl;

  std::list<std::string> pathStrings = getPathStringsBscc();

  std::list<algorithmType> runTypes = {chainBottomSingleRec};

  for(algorithmType algo : runTypes) {
    //Running all benchmark files with a single algorithm type
    std::list<algorithmType> algorithm = {algo};
    std::string fileName = algoToString(algo) + std::to_string(time(NULL)) +"dlfull";
    benchmark(pathStrings, fileName, algorithm, 0);
  }

  std::cout << "Goodbye :)" << std::endl;

  sylvan::sylvan_quit();
  lace_stop();
  return 0;
}