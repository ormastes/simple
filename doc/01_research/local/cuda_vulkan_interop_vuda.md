<!-- codex-research -->
# Local Research: CUDA/Vulkan Interop for Simple 2D and SimpleOS

Date: 2026-08-02

## Current architecture

Simple 2D currently selects CUDA or Vulkan as independent backends. CUDA owns a
driver context, PTX launches, allocations, and device-to-host readback. Vulkan
owns a Vulkan session, storage buffers, SPIR-V dispatch, presentation, and its
own readback. No allocation, semaphore, queue, context, or device identity is
shared between them.

`GraphicsSessionPolicy.interop_policy` and the CUDA/Vulkan backend adapters are
the appropriate orchestration seam. Native allocation/import/export and
semaphore operations must remain in no-GC/SFFI/runtime owners. Existing backend
names must retain their meaning; a composite interop policy must be opt-in.

SimpleOS CUDA is currently bounded host offload while Vulkan is QEMU
virtio-gpu/Venus or an Adreno/Turnip profile. Neither provides the Linux NVIDIA
RM/UVM context that the VUDA paper modifies. Therefore VUDA cannot truthfully be
implemented or environment-promoted in SimpleOS, Venus, Adreno, Metal, or an
emulator. SimpleOS may share the typed interop policy and report unavailable.

## Existing evidence and gaps

CUDA and Vulkan strict/readback tests exist independently. Missing evidence:
same physical-device UUID matching, external-memory capability negotiation,
shared allocation lifetime and bounds, CUDA-write to Vulkan-read/render,
timeline semaphore ordering, device loss cleanup, mismatch rejection, setup
cost, and independent proof of spatial concurrency.

The current host has two NVIDIA GPUs, driver 580.126.16, CUDA libraries, Vulkan
1.4, headless Vulkan, external memory/semaphore instance extensions, and an
NVIDIA Vulkan ICD. This proves prerequisites only. It does not prove CUDA and
Vulkan select the same GPU, external-object round trip, VUDA patches, or spatial
execution.

## Environment evidence classes

1. Static: libraries, extensions, driver/runtime versions.
2. Identity: CUDA and Vulkan UUIDs are exactly equal.
3. Interop: Vulkan allocation export, CUDA import/write, semaphore signal/wait,
   Vulkan render/readback checksum, cleanup.
4. Performance: bounded setup latency and steady-state no-CPU-copy receipts.
5. Spatial concurrency: profiler/counter evidence that overlap occurred. Timing
   improvement alone is insufficient.
6. VUDA: exact supported driver/toolkit build, patched kernel modules, implicit
   layer, API receipt, page-table/channel validation, and isolation tests.

Rows 3-6 must skip with a precise unsupported reason when hardware or external
libraries are absent; a skip never promotes capability.
