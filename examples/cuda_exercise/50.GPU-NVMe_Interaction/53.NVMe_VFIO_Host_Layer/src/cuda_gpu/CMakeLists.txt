# Module 55.0: Shared Implementation Libraries
# These libraries are reused by Module 55.1-55.3 and Module 56

add_library(cuda_io_gpu_mem_55 STATIC io/cuda_io_gpu_mem.cpp)
set_source_files_properties(io/cuda_io_gpu_mem.cpp PROPERTIES LANGUAGE CUDA)
target_include_directories(cuda_io_gpu_mem_55 PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(cuda_io_gpu_mem_55 PUBLIC mapping_host ${CUDA_BASIC_LIB} CUDA::cuda_driver)

add_library(mapping_gpu_55 STATIC mapper/mapper_gpu.cpp)
target_include_directories(mapping_gpu_55 PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(mapping_gpu_55 PUBLIC mapping_host host_io_host_mem ${CUDA_BASIC_LIB} CUDA::cuda_driver dl)

# Provide alias for backward compatibility during migration
add_library(nvme_vio_cuda_gpu_55 ALIAS mapping_gpu_55)

# ---- Doxygen documentation target ----
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${GPU_SHARED_DOXYGEN_DIR}/Doxyfile.in
)
