# GPU Dynamic Backend and Full Offload System Test Plan

1. Inspect the checker contract for ABI, capabilities, required operations, and
   replacement markers.
2. Execute the host-independent Vulkan/CUDA provider checker and require
   complete admission, wrong/incomplete/missing rejection, concurrent access,
   operation dispatch, unload/reload, replacement, and no static dependency.
3. Execute the host-independent Metal checker and require length-delimited byte
   and RuntimeValue conversion plus invalid-provider rejection.
4. Keep physical Vulkan, CUDA, and macOS Metal submission/readback as separate
   native rows; provider fixture success never promotes them.

Executable scenario:
`test/03_system/runtime/gpu_provider_dynamic_load_spec.spl`.

Generated manual target:
`doc/06_spec/03_system/runtime/gpu_provider_dynamic_load_spec.md`.

