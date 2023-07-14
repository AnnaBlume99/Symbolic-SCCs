#include <fstream>
#include <deque>
#include <map>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "bdd_utilities.h"
#include "print.h"

using sylvan::Bdd;
using sylvan::BddSet;

struct VarStruct {
  int varNumber;
};

Graph parseFileToGraph() {
  std::string pathName = "model.an";
  std::ifstream readFile(pathName);

  if(!readFile) {
    std::cout << "Invalid file name" << std::endl;
    std::exit(-1);
  }

  Graph result = {};
  Bdd nodes = leaf_false();
  BddSet fullCube = BddSet();
  std::deque<Relation> relations;

  std::string myText;
  std::map<std::string, VarStruct> varNames = {};
  int currentVar = 0;
  while (std::getline (readFile, myText)) {
    
    int comment = myText.find("*");
    int newVar = myText.find("[");
    int transitionLine = myText.find("->");

    //Each new relation requires a cube and a BDD defining the transition
    std::list<int> cubeVars = {};
    sylvan::Bdd relationBDD = leaf_false();

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
            return result;
          }
        } else {
          //???
          continue;
        }
      }

      //give the variable name its new number
      varNames[name] = {};
      varNames[name].varNumber = currentVar;
      currentVar += 2;
      std::cout << name << ", " << varNames[name].varNumber << std::endl;

    } else if(transitionLine != -1) {
      //this is a transition line
      // - add it to the collection
      bool findingVar = false;
      bool findingVal = false;
      bool LHS = true;
      bool LHSstartState = true;
      std::string currLHS = "";
      std::string currRHS = "";

      std::string fromString;

      //We need to create the relations and corresponding cubes
      for(int i = 0; i < myText.length(); i++){
        char c = myText[i];
        if(c == '\"') {
          findingVar = !findingVar;
          if(!findingVar){
            //Reset the variable name
            currRHS = "";
          }
        } else if(findingVar && LHS){
          if(LHS){
            currLHS += c;
          } else{
            currRHS += c;
          }
        } else if(std::isdigit(c)){
          if(LHSstartState){
            LHSstartState = !LHSstartState;
            //Get the state it goes from here (always flips, so we don't need to explicitly check what comes after the arrow)
          } else if (!LHS){
            //Get the condition states of RHS vars

            //Reset the name of the RHS variable, as we now will read a new one
            currRHS = "";
          }
          //We skip the digit in "-> 0/1"
        } else if(c == 'e'){
          LHS = false;
        } else {
          continue; //Skip rest of the information
        }
      }
      

    } else {
      //this line is whitespace or something else
      // - skip

      //Here we should end the previous relation, and initialize the new one

      continue;

    }
    //std::cout << myText << std::endl;
  }

  return result;
}
