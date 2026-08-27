# Vulkan native bounded readback API is missing

## Problem

`vulkan_sffi_read_buffer_bytes(handle, byte_count, offset)` had declared
`rt_vulkan_read_buffer_bytes`, but the native runtime exports no such symbol.
Native callers therefore reached address zero during device framebuffer
readback.

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


## Evidence

The x86 QEMU host-GPU daemon backtrace stopped at
`vulkan_sffi_read_buffer_bytes -> 0x0`. `nm` showed the symbol undefined while
`rt_vulkan_copy_from_buffer` was strongly defined in the Vulkan runtime archive.
