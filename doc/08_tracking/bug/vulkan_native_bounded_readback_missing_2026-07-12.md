# Vulkan native bounded readback API is missing

- **Status:** interpreter and native runtime device pass; source-matched Simple native receipt pending

## Problem

`vulkan_sffi_read_buffer_bytes(handle, byte_count, offset)` originally declared
`rt_vulkan_read_buffer_bytes` before every native runtime exported a compatible
symbol. Native callers therefore reached address zero during device framebuffer
readback. The symbol and nonzero-offset upload now exist; the remaining native
gap is a source-matched Simple executable receipt.

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
device checks. The remaining acceptance evidence is one source-matched Simple
native executable round trip.


## Evidence

The x86 QEMU host-GPU daemon backtrace stopped at
`vulkan_sffi_read_buffer_bytes -> 0x0`. `nm` showed the symbol undefined while
`rt_vulkan_copy_from_buffer` was strongly defined in the Vulkan runtime archive.
