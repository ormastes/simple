# Phase 2 Vulkan Engine2D closure requires unselected backend providers

## Status

Open native closure/link-provider defect found while building the strict Vulkan
feature producer with the admitted Phase 2 macOS arm64 compiler.

## Evidence

The build uses `SIMPLE_NO_STUB_FALLBACK=1`, isolated caches, the full Engine2D
entry closure, and a real Vulkan-enabled `libsimple_runtime.dylib`. Adding that
provider resolves the complete `rt_vulkan_*` set. Linking still fails because
the closure retains implementations for backends the program never selects:

- ROCm runtime exports;
- WebGPU shutdown/surface exports;
- bare-metal framebuffer surface methods;
- virtio-gpu framebuffer surface methods.

The linker correctly refuses these unresolved symbols. They must not be
papered over with generated weak nil/zero stubs.

## Required fix

Either native entry-closure specialization must remove unreachable concrete
backend implementations after the strict `"vulkan"` selection, or the hosted
GPU runtime bundle must supply explicit, typed unavailable providers for every
optional backend retained by the public Engine2D sum. Such providers must be
owned and documented runtime implementations, not generated weak stubs.

Admission is a strict build of
`src/app/wm_compare/vulkan_primitive_feature_producer.spl` with no fabricated
symbols, followed by physical-device execution and its normalized C parity
gate. Do not enable `SIMPLE_ALLOW_INTERNAL_STUBS` as a workaround.
