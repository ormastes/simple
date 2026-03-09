project(66_Model_Loading_Inference CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 66: Model Loading and Inference
# Implements checkpoint save/load, SafeTensors parsing, KV-cache management,
# and beam search for LLM inference.

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
