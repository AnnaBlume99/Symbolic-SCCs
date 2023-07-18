#include <fstream>
#include <deque>
#include <map>
#include <list>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "bdd_utilities.h"
#include "print.h"
#include "bscc.h"

using sylvan::Bdd;
using sylvan::BddSet;

struct VarStruct {
  int varNumber;
  Bdd relation;
  BddSet cube;
};

Graph parseFileToGraph(std::string pathName) {
  std::ifstream readFile(pathName);

  if(!readFile) {
    std::cout << "Invalid file name" << std::endl;
    std::exit(-1);
  }

  Graph result = {};
  result.nodes = leaf_true();
  result.cube = BddSet();

  std::string myText;
  std::map<std::string, VarStruct> varNames = {};
  int currentVar = 0;
  while (std::getline (readFile, myText)) {
    
    int comment = myText.find("*");
    int newVar = myText.find("[");
    int transitionLine = myText.find("->");

    if(comment != -1) {
      //this is a comment line
      // - skip
      continue;

    } else if(newVar != -1) {
      //this is a new variable declaration
      // - check the possible values
      bool findingName = false;
      bool findingValues = false;
      std::string name = "";
      for(int i = 0; i < myText.length(); i++) {
        char c  = myText[i];
        if(c == '\"') {
          findingName = !findingName;
          continue;
        } else if(findingName) {
          name += c;
        } else if(c == '[') {
          findingValues = true;
        } else if(c == ']') {
          findingValues = false;
        } else if(findingValues) {
          if(c == '0' || c == '1' || c == ',' || c == ' ') {
            continue;
          } else {
            std::cout << "Found weird char while parsing value for " << name << ": " << c << std::endl;
            std::cout << "Maybe the file should be booleanized?" << std::endl;
            std::exit(-1);
          }
        } else {
          //???
          continue;
        }
      }

      //give the variable name its new number and initialize relation
      varNames[name] = {};
      varNames[name].varNumber = currentVar;
      varNames[name].relation = leaf_false();
      BddSet cube = BddSet();
      cube.add(currentVar);
      varNames[name].cube = cube;

      //std::cout << name << ", " << currentVar << std::endl;

      result.cube.add(currentVar);

      currentVar += 2;

    } else if(transitionLine != -1) {
      //this is a transition line
      // - add it to the collection
      bool findingVar = false;
      bool findingVal = false;
      bool LHS = true;
      bool LHSstartState = true;
      std::string currLHS = "";
      std::string currRHS = "";

      Bdd currentLine = leaf_true();

      //We need to create the relations and corresponding cubes
      for(int i = 0; i < myText.length(); i++){
        char c = myText[i];
        if(c == '\"') {
          findingVar = !findingVar;
          if(findingVar){
            //Reset the variable name
            currRHS = "";
          }
        } else if(findingVar){
          if(LHS){
            currLHS += c;
          } else{
            currRHS += c;
          }
        } else if(std::isdigit(c)){
          if(LHSstartState) {
            LHSstartState = !LHSstartState;
            //Get the state it goes from here (always flips, so we don't need to explicitly check what comes after the arrow)

            int varNumber = varNames[currLHS].varNumber;
            if(c == '1') {
              //1->0
              currentLine = ithvar(varNumber).And(nithvar(varNumber + 1));
            } else if(c == '0') {
              //0->1
              currentLine = nithvar(varNumber).And(ithvar(varNumber + 1));
            } else {
              std::cout << "Found weird number while parsing LHS for " << currLHS << ": " << c << std::endl;
              std::cout << "Maybe the file should be booleanized?" << std::endl;
              std::exit(-1);
            }

          } else if (!LHS){
            //Get the condition states of RHS vars
            int varNumber = varNames[currRHS].varNumber;
            varNames[currLHS].cube.add(varNumber);
            if(c == '1') {
              currentLine = currentLine.And(ithvar(varNumber).And(ithvar(varNumber + 1)));
            } else if(c == '0') {
              currentLine = currentLine.And(nithvar(varNumber).And(nithvar(varNumber + 1)));
            } else {
              std::cout << "Found weird number while parsing RHS for " << currLHS << ": " << c << std::endl;
              std::cout << "Maybe the file should be booleanized?" << std::endl;
              std::exit(-1);
            }

          }
          //We skip the digit in "-> 0/1"
        } else if(c == 'e'){
          LHS = false;
        } else {
          continue; //Skip rest of the information
        }
      }

      //add currentLine to the growing BDD
      varNames[currLHS].relation = varNames[currLHS].relation.Or(currentLine);

    } else {
      //this line is whitespace or something else
      // - skip
      continue;
    }
  }

  //Build relations
  std::deque<Relation> relations;

  //build relations here
  for(const auto kv : varNames){
    VarStruct vs = kv.second;
    
    if(vs.relation == leaf_false()) {
      continue;
    }

    Relation rel = {};
    rel.cube = vs.cube;
    rel.relationBdd = vs.relation;

    relations.push_back(rel);
  }

  result.relations = relations;

  return result;
}
