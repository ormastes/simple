# Dynamic GPU Backend Provider Detail Design

## Provider admission

`runtime_native.c` owns one slot per backend. Each slot contains a lock, pinned
library handle, attempted/valid atomics, backend bit, and explicit environment
path owner:

- `SIMPLE_CUDA_PROVIDER_PATH`
- `SIMPLE_VULKAN_PROVIDER_PATH`
- `SIMPLE_METAL_PROVIDER_PATH`

Resolution is handle-local. `RTLD_DEFAULT`, preloading, and startup link
visibility are not evidence of dynamic provider admission.

## Artifacts

`scripts/build/build_simple_runtime_sffi.shs` builds CUDA and Vulkan separately
with `--no-default-features` and stages:

- `build/sffi/libsimple_gpu_cuda.{so,dylib,dll}`
- `build/sffi/libsimple_gpu_vulkan.{so,dylib,dll}`

The script does not whole-link the core-C archive into a provider DSO.

## Verification contract

`check-gpu-provider-dynload-registry.shs` builds a base executable and synthetic
providers. It proves accepted ABI/backend metadata, handle-local probe and
scalar-operation dispatch, missing/wrong-provider rejection, and absence of a
provider dependency in the base executable. Production Vulkan evidence must
add upload, compute dispatch, fence completion, device-origin readback, pixel
parity, loaded path/hash/ABI, and absence of static provider dependencies.
