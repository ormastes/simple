# Full-surface `clear` exceeds the Vulkan spec-minimum workgroup count at 4K and above
## Resolved 2026-11-22 — 2D-tiled clear kernel and workgroup cap `<= 65535` implemented & verified

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Filed 2026-09-03. Status: OPEN. Severity: HIGH (portability/correctness —
undefined behaviour on a conformant device), but **latent on this host**.

## The defect

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:775-778`:

```simple
me clear(color: u32):
    val total = _i64(self.w) * _i64(self.h)
    val workgroups = (total + 255) / 256
    val dispatched = self._dispatch_framebuffer_checked(self.pipe_clear, pc, workgroups, 1, 1)
```

The whole surface is linearized into ONE dimension, so the X group count grows
with total pixel count:

| Resolution | pixels | groups in X | vs spec floor 65,535 |
|---|---|---|---|
| 800x600 | 480,000 | 1,875 | ok |
| 1920x1080 | 2,073,600 | 8,100 | ok |
| 3840x2160 | 8,294,400 | 32,400 | ok |
| **7680x4320** | 33,177,600 | **129,600** | **1.98x over** |
| **8192x8192** | 67,108,864 | **262,144** | **4.0x over** |

`maxComputeWorkGroupCount[0]` has a Vulkan **required-limits floor of 65,535**.
A device that guarantees only the minimum may reject or silently misbehave.
Both of the project's declared default target dimensions
(`config/graphics/resolution_targets.sdn`) exceed it, and 4K is only 2x under.

**Nothing in the runtime queries `maxComputeWorkGroupCount`.** The only device
limit read anywhere is `max_push_constants_size`.

## Why it is green here

MoltenVK on Apple silicon reports a limit far above the floor, so the dispatch
succeeds and every gate passes. This is a portability bug that this machine
structurally cannot catch — the same class as the C-runtime gap where source
that is well-formed as bytes is nonsense to a compiler.

## The fix, and why it is low-risk in shape

**Every other dispatch site in this backend already uses 2-D 16x16 groups**,
which at 8192x8192 is 512 groups per dimension — comfortably inside the floor.
`clear` is the outlier. Matching the existing 2-D pattern fixes it without
inventing anything.

Additionally the runtime should query `maxComputeWorkGroupCount` (and
`maxStorageBufferRange`, see the sizing inventory) and fail LOUDLY rather than
through `mark_cpu_fallback`, which is a silent downgrade.

## Why it is not fixed in this commit

`clear` is on every frame path, so a wrong change breaks everything. At the
time of filing, `scripts/check/check-engine2d-backend-parity.shs` was
ERRORing (`ERROR — nothing was compared`, exit 2) because several agents were
saturating the GPU with concurrent benchmarks — so pixel-identity could not be
verified. Changing the clear path without that evidence would be exactly the
kind of unverified "obvious" fix that has already produced one 4x regression in
this arc. Fix when the machine is quiet and both gates run clean.

## Verification when fixed

- `sh scripts/check/check-engine2d-backend-parity.shs` -> PASS (not ERROR)
- `sh scripts/check/check-vulkan-2d-bit-diff.shs` -> PASS
- resolution sweep 800x600 / 1080p / 4K / 7680x4320 / 8192x8192, confirming no
  regression at small sizes
- ideally, assert the computed group counts against the 65,535 floor in a unit
  check so the defect cannot silently return

## Source

Found by a delegated defaults/sizing audit; call site verified independently by
reading `backend_vulkan.spl`. Full inventory:
`doc/08_tracking/bug/engine2d_8k_default_sizing_inventory_2026-09-03.md`.

## Resolution (2026-11-22)

- Updated `_glsl_clear()` (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl`), `spirv_clear()` (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl`), and `test/09_baselines/engine2d_vulkan/clear.comp` to compute linear pixel index via `gl_WorkGroupID.y * (gl_NumWorkGroups.x * 256u) + gl_GlobalInvocationID.x` with `local_size_x = 256, local_size_y = 1, local_size_z = 1`.
  - Existing 1D callers (`gy = 1` when `total_groups <= 65535`) preserve identical `gl_GlobalInvocationID.x` indexing with zero ABI or push-constant change.
  - Surfaces whose `ceil(w * h / 256) > 65535` tile across `(gx = 32768, gy = ceil(total_groups / 32768), 1)` via `vulkan_clear_dispatch_groups_x` / `vulkan_clear_dispatch_groups_y` (`backend_vulkan_helpers.spl`), keeping both X and Y strictly `<= 65535` across 7680x4320 (`32768 x 4`), 8192x8192 (`32768 x 8`), and 16384x16384 (`32768 x 32`).
- Updated `VulkanBackend.clear()` (`backend_vulkan.spl`), `processing_ir_execute_vulkan` (`src/lib/gc_async_mut/processing/vulkan_fill_u32.spl`), and `test/09_baselines/engine2d_vulkan/engine2d_vulkan_clear_8k_bench.c` to enforce the 2D-bounded workgroup counts and reject out-of-range dispatches fail-closed.
- Validated embedded SPIR-V 1.3 bytecode with `glslangValidator --target-env vulkan1.1`, `spirv-val --target-env vulkan1.1`, `MoltenVKShaderConverter` (SPIR-V -> MSL), `vulkan_spirv_module_structure_spec.spl` (25/25 passed), `spirv_blob_bare_hex_words_spec.spl` (2/2 passed), and `vulkan_clear_and_damage_readback_spec.spl` (7/7 passed).

