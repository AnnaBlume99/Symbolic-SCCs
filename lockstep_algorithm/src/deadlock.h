#ifndef DEADLOCK_H
#define DEADLOCK_H

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


std::pair<SccResult, Graph> deadlockRemoval(const Graph &fullGraph);
ReachResult sourceRemoval(const Graph &fullGraph);



#endif // DEADLOCK_H