# Vulkan specs: intermittent E1034 on `use gpu.engine2d.engine` (2026-09-12)

**Status:** fixed by canonicalising the import form. Root cause NOT reproduced; see
"Honest limits".

## Symptom

Several Vulkan engine2d specs reported `ERROR executed=0` from an unresolved
`use gpu.engine2d.engine` (E1034) in some sessions (F40/F38), while the same files
ran green on device in others (F31: `backend_vulkan_blend_cpu_parity_spec` 6/6).

## What was measured

Affected files (13 in `test/`, not the ~9 first estimated) carried a **bare**
first-segment import — `use gpu.engine2d.engine.{Engine2D}`,
`use gpu.engine2d.color.{blend}`, `use gpu.engine2d.backend_vulkan_helpers.{_pack_rect_pc}`
— with no `std.` prefix. Every green sibling
(`backend_vulkan_drawing_spec.spl`, `backend_vulkan_batch_and_clip_boundary_spec.spl`)
uses `std.gpu.…` or `std.gc_async_mut.gpu.…`. In `src/` the ratio is
**334 `std.gpu.` vs 8 bare** — `std.` is the canonical form; there is no `src/lib/gpu/`
root, so the bare form depends entirely on a first-segment fallback.

Reproduction attempts with `build/cargo-r2/release/simple` (39528776 bytes, mtime
1789199850), env `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_*`:

| variant | result |
|---|---|
| worktree repo root | 6/6 PASS |
| cwd = `test/` | 6/6 PASS |
| `SIMPLE_LIB=src` | 6/6 PASS |
| `SIMPLE_LIB=src/lib` | 6/6 PASS |
| `SIMPLE_LIB=/nonexistent` | 6/6 PASS |

So neither cwd nor `SIMPLE_LIB` is the discriminator for this binary.

The requested "(b) main checkout" comparison could **not** be run: the shared checkout
`/Users/ormastes/simple` does not contain these specs at all (81 files in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/`, none of the 13; the 3 integration specs
are absent too). Its `src/lib/gc_async_mut/gpu/engine2d/engine.spl` is also a different,
older revision (Sep 11, 168610 B vs Sep 12, 178513 B) — the shared tree is actively
rewritten by peer sessions.

E1034 is emitted by **both** compilers — pure Simple
(`src/compiler/99.loader/module_resolver/resolution.spl`) and the Rust seed
(`src/compiler_rust/compiler/src/module_resolver/resolution.rs`) — so the emitter does
not discriminate either. The residual explanation is run-time tree state (a peer
session mid-rewrite of `engine.spl` / the variant `__init__`) or a different binary.

## Fix

All 13 `test/` files rewritten from `use gpu.engine2d.X` to
`use std.gc_async_mut.gpu.engine2d.X` — fully qualified, which removes dependence on
*both* the bare first-segment fallback and the `std.gpu.` variant search (`engine.spl`,
`color.spl` and `backend_vulkan_helpers.spl` each exist under **two** variant roots,
`gc_async_mut` and `gc_sync_mut`). The resolver was deliberately **not** touched: with
no reproduction there is no evidence it is wrong, and the short form is not the
documented canonical one.

## Device results after the fix (worktree root, Vulkan on device)

```
blend_cpu_parity            6 examples, 0 failures
device_glass_blur           7 examples, 0 failures
image_exact_scratch         6 examples, 3 failures   <- pre-existing, see below
image_typed_upload          7 examples, 0 failures
rect_batch_edges            4 examples, 0 failures
rect_batch_one_dispatch     7 examples, 0 failures
rect_batch_pixel_oracle     4 examples, 0 failures
rect_batch_typed_upload     8 examples, 0 failures
engine2d_readback_present_parity        executed=3 passed=3
engine2d_vulkan_damage_scoped_mirror    6 examples, 0 failures
engine2d_vulkan_readback_unpack_cost    executed=6 passed=6
```

`backend_vulkan_image_exact_scratch_spec` fails 3 of 6 with **all** upload counters
reading zero (`packs=0 byte_fallbacks=0 scratch_resizes=0` vs expected 1/2/3) while its
two *pixel* expectations pass. That is an instrumentation/behaviour defect in the typed
image-upload counters, unrelated to module resolution; the import change cannot affect
counter values. Out of scope here — needs its own record.

The two benches (`test/05_perf/bench/vulkan_2d_c/{vk2d_bench,feature_showcase}.spl`)
were edited for consistency but not executed.

## Follow-up

- 8 remaining bare `use gpu.…` first-segment imports in `src/` — same latent fragility.
- The `image_exact_scratch` zero-counter failure above.

## Push-guard record

`check-test-tree-divergence-delta.shs 89c5e3f865d 2da3d0f82ac` →
`PASS — 3209 pre-existing offender(s), 0 introduced by this range` (base verdict is
the pre-existing repo-wide RED: `3943 diverged vs 965 baselined (3081 new,
103 fixed-but-still-baselined); 26 mirror-only`). Offender list saved by the helper to
`$TMPDIR/test_tree_divergence_preexisting.txt`; none of the 13 files edited here live
in a mirrored pair. conflict-markers PASS (14 files), tree-size PASS (base 136255 files).
