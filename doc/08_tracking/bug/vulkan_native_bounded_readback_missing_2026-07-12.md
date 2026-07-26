# Vulkan native bounded readback API is missing

- **Status:** interpreter device pass; source-matched native receipt pending

## Problem

`vulkan_sffi_read_buffer_bytes(handle, byte_count, offset)` originally declared
`rt_vulkan_read_buffer_bytes` before every native runtime exported a compatible
symbol. Native callers therefore reached address zero during device framebuffer
readback. The symbol now exists; the remaining native gap is source-matched
device evidence and nonzero-offset upload support.

The older `rt_vulkan_copy_from_buffer` export accepts a raw destination pointer,
ignores `offset`, and copies the complete buffer. The SFFI owner currently
adapts a packed byte array to that ABI only for exact-size, offset-zero reads.

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

The interpreter device round trip now passes with exact nonzero-offset bytes
and OOB rejection. Its retained log is
`build/gpu-goal/dual-abi/vulkan-live-readback-cycle3.log`. The remaining
acceptance evidence is one source-matched native device round trip with the
same checks.


## Evidence

The x86 QEMU host-GPU daemon backtrace stopped at
`vulkan_sffi_read_buffer_bytes -> 0x0`. `nm` showed the symbol undefined while
`rt_vulkan_copy_from_buffer` was strongly defined in the Vulkan runtime archive.
