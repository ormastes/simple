# Dynamic GPU Backend Provider Architecture

## Decision

Hosted Simple keeps the public `rt_cuda_*`, `rt_vulkan_*`, and `rt_metal_*`
compatibility ABI in core. Core loads one backend-specific provider through an
explicit admitted path using `RTLD_NOW | RTLD_LOCAL` or
`LoadLibrary`/`GetProcAddress`. A provider is never a native linker input.

The first admission contract exports:

- `rt_simple_gpu_provider_abi_version() -> i64`;
- `rt_simple_gpu_provider_backend_bits() -> i64`.

Core validates ABI version 1 and the requested backend bit before resolving any
operation against that exact handle. Missing paths, wrong versions, backend
mismatches, and missing symbols fail closed. Provider handles are process-pinned:
the provider exclusively owns device/session resources and opaque handles, so
unloading code while those handles may exist is invalid.

## Boundaries

- Core owns provider admission, public ABI trampolines, RuntimeValue decoding,
  provider provenance, and structured unavailability.
- Providers own CUDA contexts, Vulkan instances/devices/queues/resources, Metal
  objects, synchronization, and driver-loader handles.
- The stable boundary carries integers, opaque handles, and explicit
  pointer-plus-length loans. RuntimeValue and raw host collection layouts never
  cross between independently linked heaps.
- SimpleOS retains its static backend path; hosted operating systems use dynamic
  providers.

## Migration order

1. Admit and pin backend artifacts; route probes and scalar Vulkan operations.
2. Add raw pointer/length Vulkan operations and provenance receipts.
3. Remove hosted `libsimple_runtime.a` GPU selection from native linking.
4. Apply the same table ownership to CUDA and Metal, with Metal framework
   dependencies present only in its provider.
5. Require device execution/readback evidence before declaring a backend ready.

The current implementation covers step 1. Static hosted operation linkage and
full Engine2D readback remain release blockers, not accepted compatibility.
