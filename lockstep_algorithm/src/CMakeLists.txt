add_executable(main main.cpp
               scc.cpp
               print.cpp
               petriTranslation.cpp
               benchmark.cpp
               graph_creation.cpp
               reachability.cpp)

target_link_libraries(main PRIVATE Sylvan::Sylvan)

