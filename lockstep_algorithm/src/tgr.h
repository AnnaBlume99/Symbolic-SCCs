#ifndef TGR_H
#define TGR_H

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


std::pair<Graph, int> TGR(Graph universe);
std::pair<Graph, int> reduce(Bdd pivots, Graph universe);
std::pair<std::vector<Bdd>,int>  relationFireSets(const Graph &fullGraph);
std::pair<Graph, int> ITGR(Graph universe);


#endif // TGR_H