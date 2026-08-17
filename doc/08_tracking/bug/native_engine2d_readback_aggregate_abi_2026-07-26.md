# Native Engine2DReadback Aggregate ABI

## Status

The tagged aggregate base fix is deployed. Provider retention now reaches live
Vulkan initialization and strict creation. Readback remains unverified because
the caller resolves `Engine2DReadback.pixels` through a colliding module-local
type ID.

## Evidence

The no-stub native Vulkan executable initializes hardware, passes strict
creation, and selects `backend_name=vulkan`. The first
`Engine2D.read_pixels_with_source()` return is corrupted across the module
boundary: `pixels.len()` is `-1`, the handle and device identity are zero, and
`write_u32_pixels` segfaults while iterating the invalid array.

GDB identifies `write_u32_pixels` as the faulting frame. This is distinct from
the resolved `BackendStatus` comparison defect.

Disassembly shows `engine2d_readback_with_identity` returning the allocated
object as `pointer | 1`. LLVM `GetField` and `SetField` previously used that
tagged value directly as the GEP base.

`MirToLlvm.untag_aggregate_base_ptr` now strips the three runtime tag bits only
when the low tag equals `TAG_HEAP` (`1`), preserving legitimate raw pointers,
including 4-byte-aligned pointers on 32-bit targets. The focused executable
IR-generation regression passes 2/2 for x86_64 and RV32 read/write lowering.

## Deployment

The bounded self-rebuild produced
`build/gpu-goal/source-matched/simple`: 3 modules compiled, 682 reused, and no
bootstrap stage or cache reset. A projected C owner supplied the sole missing
`rt_string_free` definition without exporting unrelated runtime symbols.

That compiler emitted the 184-module source-matched Vulkan evidence closure.
A direct no-stub link succeeded with the existing optional-GPU provider and
current quarantine-lock provider. With provider retention forced, execution
reaches `backend_name=vulkan` and then crashes at the first readback field
access. Disassembly confirms the aggregate pointer is untagged correctly; the
producer allocates 48 bytes with `pixels` at offset 0, while the caller loads
`pixels` from offset `0x50`.

## Resume

Deploy the name-keyed field-layout precedence fix from
`native_engine2d_readback_cross_module_field_layout_2026-07-26.md`, then require
device readback, positive handle/device identity, zero mismatches, and passing
strict/parity specs.

## Triage 2026-08-17 (lane m7c_lib_async) — UNVERIFIED on this host

A native aggregate-return ABI fault: unreachable from an interpreted spec body and needing a GPU readback this host cannot perform. Not reproduced and not closed: this lane could neither exercise the path nor
find content-level evidence of a fix. Recording UNVERIFIED explicitly so it is
not mistaken for either a live confirmation or a close.
