# Native Engine2DReadback Aggregate ABI

## Status

Source fixed; source-matched compiler deployment and Vulkan rerun remain open
under TODO 580.

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

## Resume

The 2026-07-26 bounded self-rebuild populated the existing native cache with
all 685 source-matched compiler objects. Its first real link exposed the
expected missing Cranelift providers under `core-c-bootstrap`; adding the
existing bootstrap runtime path reduced the gap to only `rt_string_free`.
No bootstrap stage or cache reset ran.

The retained objects are under
`build/gpu-goal/current/native-objects-vnQiNE`. A prepared runtime overlay at
`build/gpu-goal/source-matched/runtime-overlay` combines the existing
provider-complete archives and proves ownership of both `rt_string_free` and
`rt_cranelift_iadd`. The three-attempt cap was reached before relinking.

Resume with one cached native-build using that overlay as `--runtime-path`,
then rerun the no-stub evidence archive. Require device readback, positive
handle/device identity, zero mismatches, and passing strict/parity specs.
