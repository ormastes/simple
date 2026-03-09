project(54_CUDA_Host_Memory CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Module 54 is now part of Module 53 (NVMe VFIO Host Layer)
# All implementation moved to 53.NVMe_VFIO_Host_Layer/src/cuda_host/
#
# This module provides a reference/alias interface for backward compatibility.
# The actual libraries (cuda_io_host_mem) are built in Module 53.
#
# To use CUDA host memory functionality:
#   - Link against: cuda_io_host_mem (from Module 53)
#   - Include: cuda_host/io/cuda_io_host_mem.h
#   - All source code is in ../53.NVMe_VFIO_Host_Layer/src/cuda_host/
#
# Structure:
#   src/cuda_host -> symlink to ../53.NVMe_VFIO_Host_Layer/src/cuda_host
#   test/         -> symlinks to ../53.NVMe_VFIO_Host_Layer/test/backup/

message(STATUS "========================================")
message(STATUS "Module 54: CUDA Host Memory")
message(STATUS "========================================")
message(STATUS "Module 54 is now integrated into Module 53")
message(STATUS "  - CUDA host libraries are built in Module 53")
message(STATUS "  - Link against: cuda_io_host_mem")
message(STATUS "  - Tests are built in Module 53")
message(STATUS "  - Source: ../53.NVMe_VFIO_Host_Layer/src/cuda_host/")
message(STATUS "========================================")
