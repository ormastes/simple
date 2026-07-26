# Native Engine2DReadback Aggregate ABI

## Status

Source fixed and deployed in a source-matched compiler. Vulkan readback remains
unverified because the evidence link selects the weak availability fallback
before extracting the strong Vulkan provider member.

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
current quarantine-lock provider. Execution did not crash, but availability
failed before readback because archive order satisfied
`rt_vulkan_is_available` from the weak core-C member and never extracted the
strong `rt_vulkan_provider_is_available` member.

## Resume

Fix provider extraction at the linker owner, for example by retaining the
provider-only symbol whenever a Vulkan provider archive is selected. Then
relink the retained source-matched evidence objects and require device
readback, positive handle/device identity, zero mismatches, and passing
strict/parity specs.
