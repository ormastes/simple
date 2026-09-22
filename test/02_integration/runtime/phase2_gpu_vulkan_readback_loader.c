/* Build the actual shared loader with this sidecar's private include. */
#include <runtime_dynload.c>
#ifdef PHASE2_GPU_READBACK_INCLUDE_FRAGMENT
#include "runtime_gpu_vulkan_readback_private.h"
#endif
