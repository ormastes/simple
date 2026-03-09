project(cuda_intermediate)

# Part 21: Synchronization and Atomics
add_subdirectory("21.Synchronization_and_Atomics")

# Part 22: Streams and Asynchronous Execution
add_subdirectory("22.Streams_and_Async")

# Part 23: Shared Memory
add_subdirectory("23.Shared_Memory")

# Part 24: Memory Coalescing and Bank Conflicts
add_subdirectory("24.Memory_Coalescing_and_Bank_Conflicts")

# Part 25: Dynamic Parallelism
# TEMPORARILY DISABLED: Complex CUDA device linking issue with fatbinwrap
# Error: undefined reference to `__fatbinwrap_b342fc9c_22_cuda_device_runtime_cu_186b7d10_30372'
# This requires deeper investigation of CMake's CUDA_RESOLVE_DEVICE_SYMBOLS handling
# add_subdirectory("25.Dynamic_Parallelism")

# Part 26: Cooperative Groups
add_subdirectory("26.Cooperative_Groups")

# Part 27: Multi-GPU Programming
add_subdirectory("27.Multi_GPU_Programming")

# Part 28: CUDA Libraries
# add_subdirectory("28.CUDA_Libraries")

# Part 29: cuDNN (Optional)
# add_subdirectory("29.cuDNN")