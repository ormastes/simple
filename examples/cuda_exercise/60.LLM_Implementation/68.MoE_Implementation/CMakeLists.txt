project(68_MoE_Implementation CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 68: Mixture-of-Experts Implementation
# Implements the MoE architecture from DeepSeek R1 with top-k routing,
# expert dispatch/combine kernels, and load balancing loss.

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
