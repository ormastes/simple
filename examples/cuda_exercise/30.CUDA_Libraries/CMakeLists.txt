# 30.CUDA_Libraries - CUDA library demonstrations
# This directory contains modules for cuBLAS, cuFFT, cuRAND, cuSPARSE, Thrust, cuDNN, and Tensor Cores

# Add each library module
add_subdirectory(31.cuBLAS)
add_subdirectory(32.cuFFT)
add_subdirectory(33.cuRAND)
add_subdirectory(34.cuSPARSE)
add_subdirectory(35.Thrust)
# add_subdirectory(36.cuDNN)      # Requires cuDNN library
add_subdirectory(37.GPUDirect_Storage)
add_subdirectory(38.Tensor_Cores)
