# Vulkan native bounded readback API is missing

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
