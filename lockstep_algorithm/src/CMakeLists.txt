add_executable(main main.cpp
               scc.cpp
               bscc.cpp
               print.cpp
               petriTranslation.cpp
               benchmark.cpp
               graph_creation.cpp
               interface.cpp
               reachability.cpp
               tgr.cpp
               ../test/graph_examples.cpp
               ../test/test_sccListCorrectness.cpp)

target_link_libraries(main PRIVATE Sylvan::Sylvan)

