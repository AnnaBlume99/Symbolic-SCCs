#include <fstream>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "bdd_utilities.h"
#include "print.h"

using sylvan::Bdd;
using sylvan::BddSet;

Bdd parseFileToBdd() {
  std::string pathName = "../bdd.txt";
  std::ifstream readFile(pathName);

  if(!readFile) {
    std::cout << "Invalid file name" << std::endl;
    std::exit(-1);
  }

  Bdd result = leaf_false();
  std::string myText;
  while (std::getline (readFile, myText)) {
    std::string currVar = "";
    bool varParsing = false;
    Bdd currentPath = leaf_true();
    for (int i=0; i< myText.length(); i++) {
      char val = myText[i];
      if(val == '<') {
        //start new AND-clause
        varParsing = true;
        currVar = "";

      } else if(val == '>') {
        //end current AND-clause and add it to the result
        result = result.Or(currentPath);
        std::cout << "Currentpath parsed:" << std::endl;
        printBdd(currentPath);
        currentPath = leaf_true();

      } else if(val == ':') {
        //next number is true/false
        varParsing = false;        

      } else if(val == ' ' || val == ',') {
        //skip whitespace and commas
        continue;

      } else {
        if(varParsing) {
          //Currently parsing the number assigned to the var
          currVar.push_back(val);
        } else {
          //Currently parsing the truth assignment of the var
          int varInt = stoi(currVar);
          if(val == '0') {
            //false
            currentPath = currentPath.And(nithvar(varInt));

          } else {
            //true
            currentPath = currentPath.And(ithvar(varInt));
          }
          //this assignment is done, start the next one
          varParsing = true;
          currVar = "";
        }
      }
    }
  }
  
  return result;
}
