#ifndef PARSE_H
#define PARSE_H

#include <deque>
#include<list>
#include<stack>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "petriTranslation.h"
#include "reachability.h"
#include "bdd_utilities.h"
#include "scc.h"

using sylvan::Bdd;
using sylvan::BddSet;

Graph parseFileToGraph(std::string pathName);
Graph parseFileToGraph2(std::string pathName);
#endif // PARSE_H