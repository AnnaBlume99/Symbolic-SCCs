#include <iostream>
#include <list>
#include <iterator>
#include <functional>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "graph_examples.h"
#include "../src/scc.h"
#include "../src/bscc.h"
#include "../src/bdd_utilities.h"
#include "../src/petriTranslation.h"
#include "../src/graph_creation.h"
#include "../src/benchmark.h"
#include "../src/print.h"

bool testGraph(const Graph &graph, const std::list<sylvan::Bdd> &expectedSCCs, algorithmType algorithm) {
  SccResult sccAndSteps;
  std::cout << "Called testGraph" << std::endl;
  std::list<sylvan::Bdd> result;
  switch (algorithm)
  {
    case lockstepSat:
      sccAndSteps = lockstepSaturation(graph);
      result = sccAndSteps.sccs;
      break;
    case lockstepRelUnion:
      sccAndSteps = lockstepRelationUnion(graph);
      result = sccAndSteps.sccs;
      break;
    case xbSat:
      sccAndSteps = xieBeerel<Saturation>(graph);
      result = sccAndSteps.sccs;
      break;
    case xbRelUnion:
      sccAndSteps = xieBeerel<RelationUnion>(graph);
      result = sccAndSteps.sccs;
      break;
    case xbRelUnionBottom:
      sccAndSteps = xieBeerelBottom<RelationUnion>(graph);
      result = sccAndSteps.sccs;
      break;
    case xbSatBottom:
      sccAndSteps = xieBeerelBottom<Saturation>(graph);
      result = sccAndSteps.sccs;
      break;
    case chainBottomBasic:
      sccAndSteps = chainAlgBottomBasic(graph);
      result = sccAndSteps.sccs;
      break;
    case chainBottomAdvanced:
      sccAndSteps = chainAlgBottomAdvanced(graph);
      result = sccAndSteps.sccs;
      break;
  }

  if(result.size() != expectedSCCs.size()){
    std::cout << "Too many or too few SCCs" << std::endl;
    std::cout << "Result amount: " << result.size() << std::endl;
    std::cout << "Expected amount: " << expectedSCCs.size() << std::endl;
    return false;
  }
  bool testResult = sccListCorrectness(result, expectedSCCs);
  if(!testResult) {
    std::cout << "result false, printing sccs:" << std::endl;
    std::cout << "expected: " << std::endl;
    printBddListAsString(graph.cube.size(), expectedSCCs);
    std::cout << "result: " << std::endl;
    printBddListAsString(graph.cube.size(), result);
  }
  return testResult;
}

int runWithAllAlgorithmTypes(std::string testFunctionString, std::function<bool(algorithmType)> testFunction) {
  int fails = 0;
  if(!testFunction(lockstepSat)) {
    std::cout << testFunctionString << " " << algoToString(lockstepSat) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(lockstepRelUnion)) {
    std::cout << testFunctionString << " " << algoToString(lockstepRelUnion) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(xbRelUnion)) {
    std::cout << testFunctionString << " " << algoToString(xbRelUnion) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(xbSat)) {
    std::cout << testFunctionString << " " << algoToString(xbSat) << " failed" << std::endl;
    fails++;
  }

  return fails;
}


int runWithAllBsccAlgorithms(std::string testFunctionString, std::function<bool(algorithmType)> testFunction){
  int fails = 0;
  if(!testFunction(xbRelUnionBottom)) {
    std::cout << testFunctionString << " " << algoToString(xbRelUnionBottom) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(xbSatBottom)) {
    std::cout << testFunctionString << " " << algoToString(xbSatBottom) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(chainBottomBasic)) {
    std::cout << testFunctionString << " " << algoToString(chainBottomBasic) << " failed" << std::endl;
    fails++;
  }

  if(!testFunction(chainBottomAdvanced)) {
    std::cout << testFunctionString << " " << algoToString(chainBottomAdvanced) << " failed" << std::endl;
    fails++;
  }

  return fails;

}




bool runTest(std::string testFunctionString, std::function<bool()> testFunction, bool expectedResult) {
  if(testFunction() == expectedResult) {
    return true;
  } else {
    std::cout << testFunctionString << " failed" << std::endl;
    return false; 
  }
}

bool testNoGraph(algorithmType algorithm) {
  std::list<sylvan::Bdd> expectedSCCs = {};
  const Graph graph = noGraph();
  return testGraph(graph, expectedSCCs, algorithm);
}

bool testOneNodeGraph(algorithmType algorithm) {
  std::string bitstring = "0";
  sylvan::Bdd scc1 = makeNode(bitstring);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = oneNodeGraph();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testOneNodeGraphSelfLoop(algorithmType algorithm) {
  std::string bitstring = "0";
  sylvan::Bdd scc1 = makeNode(bitstring);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = oneNodeGraphSelfLoop();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testTwoNodeGraphOneSCC(algorithmType algorithm) {
  std::string a = "0"; std::string b = "1";
  std::list<std::string> nodeList = {a,b};
  sylvan::Bdd scc1 = makeNodes(nodeList);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = twoNodeGraphOneSCC();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testTwoNodeGraphTwoSCCs(algorithmType algorithm) {
  std::string a = "0"; std::string b = "1";
  sylvan::Bdd scc1 = makeNode(a);
  sylvan::Bdd scc2 = makeNode(b);
  std::list<sylvan::Bdd> expectedSccList = {scc1,scc2};

  const Graph graph = twoNodeGraphTwoSCCs();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testTwoNodeGraphTwoRelations(algorithmType algorithm) {
  std::string a = "0"; std::string b = "1";
  std::list<std::string> nodeList = {a,b};
  sylvan::Bdd scc1 = makeNodes(nodeList);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = twoNodeGraphTwoRelations();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testNonConnectedGraph(algorithmType algorithm) {
  std::string a = "0"; std::string b = "1";
  sylvan::Bdd scc1 = makeNode(a);
  sylvan::Bdd scc2 = makeNode(b);
  std::list<sylvan::Bdd> expectedSccList = {scc1,scc2};

  const Graph graph = nonConnectedGraph();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testfourNodesOneRelation(algorithmType algorithm) {
  std::string a = "00"; std::string b = "01";
  std::string c = "10"; std::string d = "11";
  std::list<std::string> nodeList = {a,b,c,d};
  sylvan::Bdd scc1 = makeNodes(nodeList);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = twoNodeGraphTwoRelations();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample1oneRel(algorithmType algorithm) {
  std::string zero = "0000";
  std::string one =  "0001";
  std::string two =  "0010";
  std::string three ="0011";
  std::string four = "0100";
  std::string five = "0101";
  std::string six =  "0110";
  std::string seven ="0111";
  std::string eight ="1000";

  std::list<std::string> nodeList1 = {zero,one,two};
  std::list<std::string> nodeList2 = {three};
  std::list<std::string> nodeList3 = {four};
  std::list<std::string> nodeList4 = {five,six,seven};
  std::list<std::string> nodeList5 = {eight};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);
  std::list<sylvan::Bdd> expectedSccList = {scc1, scc5, scc3, scc4, scc2};

  const Graph graph = graphExample1oneRel();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample1multRel(algorithmType algorithm) {
  std::string zero  = "0000";
  std::string one   = "0001";
  std::string two   = "0010";
  std::string three = "0011";
  std::string four  = "0100";
  std::string five  = "0101";
  std::string six   = "0110";
  std::string seven = "0111";
  std::string eight = "1000";

  std::list<std::string> nodeList1 = {zero,one,two};
  std::list<std::string> nodeList2 = {three};
  std::list<std::string> nodeList3 = {four};
  std::list<std::string> nodeList4 = {five,six,seven};
  std::list<std::string> nodeList5 = {eight};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);
  std::list<sylvan::Bdd> expectedSccList = {scc1, scc5, scc3, scc4, scc2};

  const Graph graph = graphExample1multRel();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample2oneRel(algorithmType algorithm) {
  std::string n0 = "00000"; std::string n1 = "00001";
  std::string n2 = "00010"; std::string n3 = "00011";
  std::string n4 = "00100"; std::string n5 = "00101";
  std::string n6 = "00110"; std::string n7 = "00111";
  std::string n8 = "01000"; std::string n9 = "01001";
  std::string n10 = "01010"; std::string n11 = "01011";
  std::string n12 = "01100"; std::string n13 = "01101";
  std::string n14 = "01110"; std::string n15 = "01111";
  std::string n16 = "10000"; std::string n17 = "10001";
  std::string n18 = "10010"; std::string n19 = "10011";
  std::string n20 = "10100";

  std::list<std::string> nodeList1 = {n0};
  std::list<std::string> nodeList2 = {n1,n2};
  std::list<std::string> nodeList3 = {n3,n4,n5};
  std::list<std::string> nodeList4 = {n6,n7,n8,n9};
  std::list<std::string> nodeList5 = {n10,n11,n12,n13,n14};
  std::list<std::string> nodeList6 = {n15,n16,n17,n18,n19,n20};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);
  sylvan::Bdd scc6 = makeNodes(nodeList6);
  std::list<sylvan::Bdd> expectedSccList = {scc1, scc6, scc4, scc5, scc3, scc2};

  const Graph graph = graphExample2oneRel();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample2multRel(algorithmType algorithm) {
  std::string n0 = "00000"; std::string n1 = "00001";
  std::string n2 = "00010"; std::string n3 = "00011";
  std::string n4 = "00100"; std::string n5 = "00101";
  std::string n6 = "00110"; std::string n7 = "00111";
  std::string n8 = "01000"; std::string n9 = "01001";
  std::string n10 = "01010"; std::string n11 = "01011";
  std::string n12 = "01100"; std::string n13 = "01101";
  std::string n14 = "01110"; std::string n15 = "01111";
  std::string n16 = "10000"; std::string n17 = "10001";
  std::string n18 = "10010"; std::string n19 = "10011";
  std::string n20 = "10100";

  std::list<std::string> nodeList1 = {n0};
  std::list<std::string> nodeList2 = {n1,n2};
  std::list<std::string> nodeList3 = {n3,n4,n5};
  std::list<std::string> nodeList4 = {n6,n7,n8,n9};
  std::list<std::string> nodeList5 = {n10,n11,n12,n13,n14};
  std::list<std::string> nodeList6 = {n15,n16,n17,n18,n19,n20};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);
  sylvan::Bdd scc6 = makeNodes(nodeList6);
  std::list<sylvan::Bdd> expectedSccList = {scc1, scc6, scc4, scc3, scc2, scc5};

  const Graph graph = graphExample2multRel();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample3oneRel(algorithmType algorithm) {
  std::string a = "000"; std::string b = "001";
  std::string c = "010"; std::string d = "011"; std::string e = "100";
  std::list<std::string> nodeList = {a,b,c,d,e};
  sylvan::Bdd scc1 = makeNodes(nodeList);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = graphExample3oneRel();
  return testGraph(graph, expectedSccList, algorithm);
}

bool testGraphExample3multRel(algorithmType algorithm) {
  std::string a = "000"; std::string b = "001";
  std::string c = "010"; std::string d = "011"; std::string e = "100";
  std::list<std::string> nodeList = {a,b,c,d,e};
  sylvan::Bdd scc1 = makeNodes(nodeList);
  std::list<sylvan::Bdd> expectedSccList = {scc1};

  const Graph graph = graphExample3multRel();
  return testGraph(graph, expectedSccList, algorithm);
}





bool testBscc1oneRel(algorithmType algorithm) {
  std::string n0 = "000";
  std::string n1 = "001";
  std::string n2 = "010";
  std::string n3 = "011";
  std::string n4 = "100";
  std::string n5 = "101";
  std::string n6 = "110";

  std::list<std::string> nodeList1 = {n2};
  std::list<std::string> nodeList2 = {n3};
  std::list<std::string> nodeList3 = {n4};
  std::list<std::string> nodeList4 = {n5,n6};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);

  std::list<sylvan::Bdd> expectedSccList = {scc1, scc2, scc3, scc4};

  const Graph graph = graphExampleBscc1oneRel();
  return testGraph(graph, expectedSccList, algorithm);

}

bool testBscc1multRel(algorithmType algorithm) {
  std::string n0 = "000";
  std::string n1 = "001";
  std::string n2 = "010";
  std::string n3 = "011";
  std::string n4 = "100";
  std::string n5 = "101";
  std::string n6 = "110";

  std::list<std::string> nodeList1 = {n2};
  std::list<std::string> nodeList2 = {n3};
  std::list<std::string> nodeList3 = {n4};
  std::list<std::string> nodeList4 = {n5,n6};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);

  std::list<sylvan::Bdd> expectedSccList = {scc1, scc2, scc3, scc4};

  const Graph graph = graphExampleBscc1multRel();
  return testGraph(graph, expectedSccList, algorithm);

}

bool testBscc2oneRel(algorithmType algorithm) {
  std::string n0 = "0000";
  std::string n1 = "0001";
  std::string n2 = "0010";
  std::string n3 = "0011";
  std::string n4 = "0100";
  std::string n5 = "0101";
  std::string n6 = "0110";
  std::string n7 = "0111";
  std::string n8 = "1000";

  std::list<std::string> nodeList1 = {n4};
  std::list<std::string> nodeList2 = {n5};
  std::list<std::string> nodeList3 = {n6};
  std::list<std::string> nodeList4 = {n7};
  std::list<std::string> nodeList5 = {n8};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);

  std::list<sylvan::Bdd> expectedSccList = {scc1, scc2, scc3, scc4, scc5};

  const Graph graph = graphExampleBscc2oneRel();
  return testGraph(graph, expectedSccList, algorithm);

}


bool testBscc3oneRel(algorithmType algorithm) {
  std::string n0 = "00000";
  std::string n1 = "00001";
  std::string n2 = "00010";
  std::string n3 = "00011";
  std::string n4 = "00100";
  std::string n5 = "00101";
  std::string n6 = "00110";
  std::string n7 = "00111";
  std::string n8 = "01000";
  std::string n9 = "01001";
  std::string n10 = "01010";
  std::string n11 = "01011";
  std::string n12 = "01100";
  std::string n13 = "01101";
  std::string n14 = "01110";
  std::string n15 = "01111";
  std::string n16 = "10000";
  std::string n17 = "10001";
  std::string n18 = "10010";



  std::list<std::string> nodeList1 = {n4};
  std::list<std::string> nodeList2 = {n5};
  std::list<std::string> nodeList3 = {n6};
  std::list<std::string> nodeList4 = {n7};
  std::list<std::string> nodeList5 = {n8};
  std::list<std::string> nodeList6 = {n13};
  std::list<std::string> nodeList7 = {n14};
  std::list<std::string> nodeList8 = {n15};
  std::list<std::string> nodeList9 = {n16};
  std::list<std::string> nodeList10 = {n17};
  sylvan::Bdd scc1 = makeNodes(nodeList1);
  sylvan::Bdd scc2 = makeNodes(nodeList2);
  sylvan::Bdd scc3 = makeNodes(nodeList3);
  sylvan::Bdd scc4 = makeNodes(nodeList4);
  sylvan::Bdd scc5 = makeNodes(nodeList5);
  sylvan::Bdd scc6 = makeNodes(nodeList6);
  sylvan::Bdd scc7 = makeNodes(nodeList7);
  sylvan::Bdd scc8 = makeNodes(nodeList8);
  sylvan::Bdd scc9 = makeNodes(nodeList9);
  sylvan::Bdd scc10 = makeNodes(nodeList10);

  std::list<sylvan::Bdd> expectedSccList = {scc1, scc2, scc3, scc4, scc5, scc6, scc7, scc8, scc9, scc10};

  const Graph graph = graphExampleBscc3oneRel();
  return testGraph(graph, expectedSccList, algorithm);

}