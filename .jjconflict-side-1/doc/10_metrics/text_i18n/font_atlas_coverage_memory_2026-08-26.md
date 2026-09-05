# Shared font-atlas coverage and memory — 2026-08-26

The third/final bounded composite-owner cycle passes 7/7 examples with 100%
of 10 instrumented Simple decisions and 32% lines (35/107). Coverage includes
cache identity, invalid geometry, bounds and integer overflow, insufficient
atlas storage, alpha tinting, destination origin, versioning, and generated
source ownership for OpenCL, HIP, CUDA, Metal, modern Vulkan, and legacy Vulkan.

Generated kernel conditionals are source text and are not included in the
Simple branch result. Backend compilation, dispatch, device execution, fence,
and readback coverage remain mandatory.

The CPU memory lane passes 2/2. It performs 256 32x32 extracts from a 64x64
atlas (16,384 atlas bytes; 1,048,576 cumulative output bytes) and proves
Engine2D/Engine3D cache identities remain distinct. Runtime allocation/RSS
counters and all GPU memory fields are unavailable; no zero-allocation or VRAM
claim is made.
