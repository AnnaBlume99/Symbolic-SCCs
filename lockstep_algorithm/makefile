.PHONY: clean build test coverage

MAKE_FLAGS=-j $$(nproc)

# ============================================================================ #
#  BUILD
# ============================================================================ #
build:
	@mkdir -p build/ && cd build/ && cmake -D CMAKE_BUILD_TYPE=Release ..

# ============================================================================ #
#  MAIN program for small tests
# ============================================================================ #
M = 1024

main:
	@mkdir -p build/
	@cd build/ && cmake -D CMAKE_BUILD_TYPE=Debug \
                      -D CMAKE_C_FLAGS=$(O3_FLAGS) \
                      -D CMAKE_CXX_FLAGS=$(O3_FLAGS) \
                ..
	@cd build/ && make $(MAKE_FLAGS) main
	@echo "" && echo ""
	@./build/src/main ${M}

test:
	@mkdir -p build/
	@cd build/ && cmake -D CMAKE_BUILD_TYPE=Debug \
                      -D CMAKE_C_FLAGS=$(O2_FLAGS) \
                      -D CMAKE_CXX_FLAGS=$(O2_FLAGS) \
                ..
	@cd build/ && make $(MAKE_FLAGS) test
	@echo "" && echo ""
	@./build/test/test ${M}