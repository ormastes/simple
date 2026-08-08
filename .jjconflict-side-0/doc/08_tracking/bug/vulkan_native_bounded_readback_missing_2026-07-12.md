# Vulkan Native Bounded Readback Repair

- **Status:** resolved on Linux 2026-07-26

## Problem

`vulkan_sffi_read_buffer_bytes(handle, byte_count, offset)` originally declared
`rt_vulkan_read_buffer_bytes` before every native runtime exported a compatible
symbol. Native callers therefore reached address zero during device framebuffer
readback. The symbol, nonzero-offset upload, and source-matched Simple native
receipt now exist.

The legacy typed `rt_vulkan_copy_from_buffer` export still cannot safely mutate
interpreter arrays. New callers use array-returning bounded readback, while
compiled callers use the raw core-C destination ABI.

## Required fix

Add one native runtime facade that accepts `(handle, byte_count, offset)`, checks
all bounds, honors the offset, and returns or fills a packed byte array through
the normal Simple array ABI. Register it in native/interpreter symbol tables and
cover nonzero offsets, short reads, invalid handles, and destination bounds.

Then remove the pointer shim and TODO from
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`.

## 2026-07-26 dual-ABI repair

The Rust runtime and interpreter now expose the bounded array-returning API,
while pure-Simple native arrays still require the raw core-C ABI. The SFFI
owner selects the typed API through `rt_is_interpreter_runtime()`, which is
true only in interpreter dispatch and false in compiled runtimes. Upload,
SPIR-V compilation, push constants, and bounded readback share that policy.
Legacy in-place readback fails closed in the interpreter because interpreter
arrays use copy-on-write values; callers must use
`vulkan_sffi_read_buffer_bytes`.

The interpreter device round trip passes with exact nonzero-offset bytes and
OOB rejection. Its retained log is
`build/gpu-goal/dual-abi/vulkan-live-readback-cycle3.log`. The native Rust
runtime test `native_vulkan_upload_honors_nonzero_offset` passes the same real
device checks. A source-matched Simple native executable now returns eight
exact `0x01020304` values with positive handle and identity. The same executable
passes unavailable, init, submit, readback, and mismatch fault phases with exact
typed reasons, empty output, and zero failure provenance.


## Evidence

The x86 QEMU host-GPU daemon backtrace stopped at
`vulkan_sffi_read_buffer_bytes -> 0x0`. `nm` showed the symbol undefined while
`rt_vulkan_copy_from_buffer` was strongly defined in the Vulkan runtime archive.

Current native evidence is retained under
`build/simpleos_gpu_host/vulkan_fault_native/`. The runtime archive SHA-256 is
`2e760130f98d14e7498c29903f9bd2605d55e0e3d7d9224282c1661c107ff704`.
Run `sh scripts/check/check-processing-vulkan-fault-native.shs`.
