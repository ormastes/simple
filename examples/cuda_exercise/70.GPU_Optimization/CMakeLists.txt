project(70_GPU_Optimization)

# Find required packages
find_package(CUDAToolkit REQUIRED)
find_package(Threads REQUIRED)

# Check for Python (required for PyCUDA wrappers)
find_package(Python3 COMPONENTS Interpreter Development)
if(Python3_FOUND)
    message(STATUS "Found Python ${Python3_VERSION}: ${Python3_EXECUTABLE}")
else()
    message(WARNING "Python not found. PyCUDA wrappers will be disabled.")
endif()

# Check for PyTorch (optional but recommended for Parts 76-77)
if(Python3_FOUND)
    execute_process(
        COMMAND ${Python3_EXECUTABLE} -c "import torch; print(torch.__version__)"
        OUTPUT_VARIABLE TORCH_VERSION
        OUTPUT_STRIP_TRAILING_WHITESPACE
        ERROR_QUIET
        RESULT_VARIABLE TORCH_RESULT
    )

    if(TORCH_RESULT EQUAL 0)
        message(STATUS "Found PyTorch ${TORCH_VERSION}")
        set(HAS_PYTORCH ON)
    else()
        message(STATUS "PyTorch not found. Parts 76-77 will have limited functionality.")
        set(HAS_PYTORCH OFF)
    endif()
endif()

# Check for cuBLAS (for performance comparisons)
find_package(CUDAToolkit REQUIRED COMPONENTS cublas)

# Optional: Check for cuDNN
find_library(CUDNN_LIB cudnn PATHS ${CUDAToolkit_LIBRARY_DIR} /usr/local/cuda/lib64)
if(CUDNN_LIB)
    message(STATUS "Found cuDNN library: ${CUDNN_LIB}")
    set(HAS_CUDNN ON)
else()
    message(STATUS "cuDNN not found. Some optimizations in Part 73 will be disabled.")
    set(HAS_CUDNN OFF)
endif()

# Check if Part 50 (GPU-NVMe Interaction) is available for Part 75
if(EXISTS "${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/CMakeLists.txt")
    set(HAS_NVME_SUPPORT ON)
    message(STATUS "Found Part 50 (GPU-NVMe Interaction). NVMe data loading in Part 75 enabled.")
else()
    set(HAS_NVME_SUPPORT OFF)
    message(STATUS "Part 50 not found. Part 75 will use standard file I/O.")
endif()

# Add subdirectories for each module
add_subdirectory(71.MatMul_CPU_PyCUDA)
add_subdirectory(72.Backprop_CPU_PyCUDA)
add_subdirectory(73.Attention_CPU_PyCUDA)
add_subdirectory(74.Experts_CPU_PyCUDA)
add_subdirectory(75.NVMe_CPU_Memory)
add_subdirectory(76.PyTorch_C_API)
add_subdirectory(77.PyTorch_Native_CUDA)
add_subdirectory(78.Progressive_Optimizations)
add_subdirectory(79.Memory_Analysis)
