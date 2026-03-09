project(56_GPU_Queue_GPU_Buffer CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 56: GPU Queue + GPU Buffer - Fully GPU-Initiated NVMe I/O
#
# This module supports multiple doorbell modes from Module 55:
#   - 55.1: Host Daemon Doorbell (universal compatibility)
#   - 55.2: DBC Shadow Doorbell (requires DBC-capable NVMe)
#   - 55.3: Host DBC Doorbell (DBC-like API without hardware DBC)
#   - 56:   Direct MMIO (GPU writes MMIO doorbells)
#
# All GPU components (queue, PRP, buffer, doorbell) work in GPU memory
# for all modes, ensuring consistent GPU code across different hardware.

# ---- DBC Capability Checker Tool ----
# Use the check_nvme_dbc tool from Module 55.2 instead of building a duplicate

# ---- Kernel module (not built by CMake - for documentation only) ----
# The kernel module in driver/src/gpu_g2p_map_module.c should be built with kbuild
#
# To build the driver:
#   cd driver && make
#   sudo insmod gpu_g2p_map_module.ko

# Note: Tests are built through Module 53 (via symbolic links)
# Don't add test subdirectory here to avoid duplicate targets

# Print configuration summary
message(STATUS "")
message(STATUS "═══════════════════════════════════════════════════════════")
message(STATUS "Module 56: GPU Queue + GPU Buffer Configuration")
message(STATUS "═══════════════════════════════════════════════════════════")
message(STATUS "Doorbell modes supported:")
message(STATUS "  - Host Daemon (55.1):   Universal compatibility")
message(STATUS "  - DBC Shadow (55.2):    Requires DBC-capable NVMe")
message(STATUS "  - Host DBC (55.3): DBC API without hardware DBC")
message(STATUS "  - Direct MMIO (56):     GPU writes MMIO doorbells")
message(STATUS "")
message(STATUS "Check NVMe DBC support:")
message(STATUS "  Use tool from Module 55.2:")
message(STATUS "  cd ../55.CUDA_GPU_Memory/55.2_DBC_Shadow_Doorbell")
message(STATUS "  sudo ./check_nvme_dbc /dev/nvme0")
message(STATUS "")
message(STATUS "All GPU components (queue, PRP, buffer, doorbell) work")
message(STATUS "in GPU memory for ALL modes.")
message(STATUS "═══════════════════════════════════════════════════════════")
message(STATUS "")
