# Native Engine2DReadback Aggregate ABI

## Status

Open. TODO 580 Vulkan evidence blocker.

## Evidence

The no-stub native Vulkan executable initializes hardware, passes strict
creation, and selects `backend_name=vulkan`. The first
`Engine2D.read_pixels_with_source()` return is corrupted across the module
boundary: `pixels.len()` is `-1`, the handle and device identity are zero, and
`write_u32_pixels` segfaults while iterating the invalid array.

GDB identifies `write_u32_pixels` as the faulting frame. This is distinct from
the resolved `BackendStatus` comparison defect.

## Resume

Fix cached LLVM lowering for class aggregates containing arrays, then rerun the
existing no-stub evidence archive. Require device readback, positive
handle/device identity, zero mismatches, and passing strict/parity specs.
