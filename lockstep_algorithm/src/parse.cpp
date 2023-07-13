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
      
      

    } else {
      //this line is whitespace or something else
      // - skip
      continue;

    }
    //std::cout << myText << std::endl;
  }

  return result;
}
