project(26_Cooperative_Groups CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 26: Cooperative Groups
# Demonstrates cooperative groups features that improve upon Module 25's
# dynamic parallelism with better performance and more flexible synchronization.
#
# Key improvements over Module 25:
# - Warp shuffles instead of shared memory (2-3x faster)
# - Warp aggregation for atomics (5-10x fewer atomic operations)
# - Grid-wide synchronization (eliminates recursive kernel launches)
# - Zero kernel launch overhead vs ~5-10μs per launch

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
