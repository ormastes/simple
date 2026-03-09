# Part 50: GPU-NVMe Interaction
# Aggregates GPU-NVMe modules under the root build/ tree.

# Shared performance test library
add_subdirectory(00.perf_common)

# Modules with buildable code/docs
add_subdirectory(53.NVMe_VFIO_Host_Layer)
add_subdirectory(54.CUDA_Host_Memory)
add_subdirectory(56.GPU_Queue_GPU_Buffer)
add_subdirectory(57.Performance_Comparison_GDS_vs_GPU)
# add_subdirectory(58.Simple_GPU_Filesystem_API)  # TODO: Re-enable when host_io_read/write APIs are implemented
add_subdirectory(59.Attention_Expert_Dynamic_Load)
