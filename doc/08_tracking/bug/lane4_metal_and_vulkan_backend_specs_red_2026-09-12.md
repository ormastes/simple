# Lane 4 triage: `metal_msl_pipeline_spec` 7/5, `backend_vulkan_drawing_spec` 40/44

**Status:** PARTIALLY RESOLVED — section 2 (`backend_vulkan_drawing_spec`) is
RESOLVED 2026-09-12, now **44/44** on this M4. Section 1 (`metal_msl_pipeline_spec`)
stays OPEN, unchanged: both specs are CORRECT and section 1 stays RED. Neither failure is fixable
inside Lane 4's file scope; the exact edits each needs are named below.

**Date:** 2026-09-12 · **Host:** Apple M4, macOS · `origin/main` = `b9667d6584f`
**Runner:** `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
build/cargo-r2/release/simple run <spec>` (39,368,072 B, mtime 1789171430)

## 1. `test/02_integration/rendering/metal_msl_pipeline_spec.spl` — 7 examples, 5 failures

```
✗ MSL compiles: all compute pipelines created        expected 0 to be greater than 0
✗ device glass dispatch owns an independent completed operation
                                                     array index out of bounds: index is 0 but length is 0
✗ normal mirror mode rejects a device-only glass receipt
                                                     array index out of bounds: index is 68 but length is 0
✗ GPU clear dispatch runs (1d) and marks dirty       expected false to equal true
✗ GPU rect_filled dispatch runs (2d) and marks dirty  expected false to equal true
```

> **CORRECTED 2026-09-12 — read this first.** The "registration gap" /
> "fail-open somewhere between them" framing below is wrong. Under a seed built
> WITH the `metal` feature (`build/cargo-r2/release/simple`, 39,178,424 B, mtime
> 1789197971) `metal_sffi_create_device(0)` answers a non-zero device, the
> pipelines compile, and `read_pixels()` really is a device download. There is no
> fail-open to fix: the earlier binary simply lacked the `metal` cargo feature.
> With that seed the readback spec's remaining failures were four STALE SPEC
> ORACLES, not device defects, and the backend needed no change at all. See
> `doc/08_tracking/bug/metal_engine2d_readback_device_defects_2026-09-12.md`.

**This is not an MSL source defect.** The Metal runtime is not functional in this
binary on a real Apple M4. Direct probe:

```
use std.io.metal_sffi.{metal_sffi_create_device}
fn main():
    print "device={metal_sffi_create_device(0)}"
```
→ `device=0`

`rt_metal_create_compute_pipeline` / `rt_metal_create_device` ARE present in the
binary's string table (7 hits each) and backed in
`src/compiler_rust/runtime/src/metal_graphics_runtime.rs`, so this is a
registration / feature-gate gap in the deployed seed, not a missing
implementation — the `unregistered extern silently returns nil` class
(`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`), which is why
a zero handle propagates as `0` rather than an error. The four downstream
failures all cascade from a device handle of 0: an empty session yields empty
pipeline arrays (`length is 0`) and dispatches that never mark dirty.

Every example already guards on `is_macos()` and asserts real handles, so the
spec is a correct device spec and is left RED per
`.claude/rules/testing.md` ("a correct spec that fails is a legitimate artifact").

**Not investigated further, deliberately:** one open thread remains —
`MetalBackend.init` (`src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:416-438`)
fails closed on `session.init()` returning false, and
`metal_session.spl:161` fails closed on any zero pipeline handle, yet the spec
observed `init` returning `true` WITH zero pipelines. Those three facts cannot all
hold, so there is a fail-open somewhere between them. That is a real defect worth
one focused cycle, but it is downstream of a device handle of 0 and cannot be
verified on this host until the Metal runtime answers a non-zero device.
**Unblock:** a binary whose Metal runtime registers (`metal_sffi_create_device(0)
!= 0`), then re-run the spec; if `init` still returns true with zero pipelines,
fix that fail-open first.

## 2. `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` — 44 examples, 4 failures

```
✗ retains multiple image sources through one frame batch fence
      expected 0 to equal 256
✗ fails closed for every primitive whose Vulkan pipeline is unavailable
      expected framebuffer-dispatch-failed to equal gradient-rect-dispatch-failed
✗ routes clear and filled rectangle through the same checked provenance owner
      expected framebuffer-dispatch-failed to equal clear-dispatch-failed
✗ preserves the first primitive failure reason across later failures
      expected framebuffer-dispatch-failed to equal rect-outline-dispatch-failed
```

**All four need `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan*.spl`, which
agent F21 owns right now** (hard boundary for this lane — not edited).

Exact edits required, for whoever owns those files next:

- Three of the four are one defect: the primitive dispatch path reports the
  generic owner reason `framebuffer-dispatch-failed` instead of the per-primitive
  reason the provenance contract promises. `_dispatch_framebuffer_checked`
  (`backend_vulkan.spl:1013` and its siblings) must take, or its callers must
  substitute, a per-primitive reason token — `clear-dispatch-failed`,
  `rect-outline-dispatch-failed`, `gradient-rect-dispatch-failed` — so the first
  recorded failure reason names the primitive that actually failed. Without it
  "preserves the FIRST failure reason" is untestable, because every reason is
  identical.
- `retains multiple image sources through one frame batch fence` reads back 0
  pixels where 256 are expected: the second image source is dropped across the
  frame batch fence. Same file family.

Nothing in this lane's scope (`scripts/gui/macos-gui-run.shs`,
`src/os/compositor/host_compositor_core.spl`,
`scripts/check/check-vulkan-2d-c-compare.shs`, Metal backends) affects these four.

## Related, fixed in the same change

`test/02_integration/gpu/engine2d_readback_present_parity_spec.spl` was 3/1
failing on its third example and is now 3/0 — see
`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl`, which now reports
`parity_frames=` / `frame_mismatches=`. Real-device run on this M4:
`device=Apple M4 ... samples=300 parity_frames=4 frame_mismatches=0`, confirming
the original "checksum alternates by frame parity" symptom was the bench's own
self-cancelling accumulator and not a two-buffer present.


## RESOLUTION — section 2 only, 2026-09-12

`backend_vulkan_drawing_spec` is **44 examples, 0 failures** on this M4 with the
same runner line as above. Two fixes, both pure Simple:

1. **Per-primitive dispatch reasons.** `_dispatch_framebuffer_checked`
   (`backend_vulkan_helpers.spl`) now takes a `reason: text` and records THAT
   instead of the generic `framebuffer-dispatch-failed`. All eight call sites in
   `backend_vulkan.spl` pass their own token (`clear-`, `rect-outline-`,
   `rect-`, `axis-line-rect-`, `line-`, `circle-filled-`, `triangle-filled-`,
   `gradient-rect-dispatch-failed`); the four now-dead caller-side
   `mark_cpu_fallback` calls were deleted (first-wins had already fired inside).
   F5's resync semantics (`pending_before == 0` retry, `completion_unknown`
   clearing) are untouched. The `vk2d_bench.spl` call site was updated for the
   new arity.
2. **The `pending_compute_sources.len() == 256` receipt.** The diagnosis above
   ("second image source dropped, reads back 0 pixels") was **wrong**: the
   pixels assertion `[red, bg, bg, green]` already passed; only the post-fence
   table length failed. The three pending tables are now a **block-grown slot
   table** (`_ensure_pending_compute_slot`, blocks of
   `VK_IMAGE_SOURCE_POOL_CAPACITY = 256`) assigned at
   `[self.pending_compute_count]`, and `_clear_pending_compute_state` zeroes the
   slots in place instead of reallocating. A fresh backend still starts at
   length 0, so R6's "no preallocated dispatch ceiling" holds and no
   `count >= len()` ceiling can force a mid-frame flush.

**Evidence (device, one run at a time, `build/cargo-r2/release/simple`
39368072 B mtime 1789171430):**

| spec | before | after |
|---|---|---|
| `backend_vulkan_drawing_spec` | 44/40 (4 failures) | **44/44** |
| `backend_vulkan_batch_and_clip_boundary_spec` | 7/7 | 7/7 |
| `engine2d_vulkan_readback_unpack_cost_spec` | — | 6/6 |
| `engine2d_vulkan_damage_scoped_mirror_spec` | — | 6/6 |
| `backend_vulkan_rect_batch_typed_upload_spec` | — | 8/8 |
| `vulkan_engine2d_frame_batch_contract_spec` | was RED (its `[count] = d_src` text was absent) | 3/3 |

**Sabotage proof:** reverting the gradient token to
`"framebuffer-dispatch-failed"` → 43/44 (1 failure); restored → 44/44.
