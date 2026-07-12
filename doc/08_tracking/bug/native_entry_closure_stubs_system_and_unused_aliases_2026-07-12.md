# Native entry closure stubs system symbols and unused aliases

## Symptom

Building `src/app/simpleos_gpu_host/main.spl` with `--entry-closure` and the
Vulkan core-C runtime emits eight fallback stubs even though the linked system
libraries and Vulkan runtime are present:

- `_Unwind_DeleteException`, `_Unwind_RaiseException`
- `cfgetispeed`, `cfgetospeed`, `cfsetspeed`
- `nogc_async_mut__io__SyncTcpListener`, `nogc_async_mut__io__SyncTcpStream`
- `panic`

The resulting binary strongly defines the required `rt_vulkan_*` functions but
is not acceptable for production because native-build generated fallback code.

## Reproduction

Use the host GPU daemon native-build command in
`.spipe/simpleos-qemu-host-gpu-2d/state.md`. The build log reports
`Generating 8 stub functions for unresolved symbols`.

## Expected

Entry-closure should omit unused aliased TCP globals and let the native linker
resolve supported libc/libgcc symbols. A strict mode should fail instead of
generating executable fallbacks for unresolved symbols.

## Evidence

`build/simpleos_gpu_host/vulkan-narrow-build.log` contains the exact unresolved
set. `nm -g --defined-only build/simpleos_gpu_host/simpleos_gpu_host.vulkan-narrow`
shows all five required Vulkan gates as strong `T` symbols while the generated
fallbacks remain weak definitions.
