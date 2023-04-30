This is a tool for benchmarking symbolic SCC algorithms.

The tool is run by running "make main" in the scc_algorithms folder.

In main.cpp you can specify which algorithms and benchmarks you want to run.
- The "runTypes" list is a list of algorithms to run.
The options are:
  lockstepSat, (lockstep with saturation)
  lockstepRelUnion, (lockstep without saturation)
  xbSat, (forward-backward with saturation)
  xbRelUnion, (forward-backward without saturation)
  skeleton, 
  chain
- "pathStrings" is a list of paths to PNML files that the algorithms should be run on
The tool only supports 1-safe Petri Nets (and we make no guarantees that it runs on every PNML file).
"getPathStringsFast()" and "getPathStringsSlow()" gives two possible lists of benchmarks.
The PNML files are in the PNMLFiles folder, where more can be added.

Running main will output a .csv file with the results. The results will also be printed to the terminal.