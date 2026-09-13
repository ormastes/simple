# `reason=pixel-mismatch` on the web Draw IR Vulkan lane is NOT a pixel mismatch (Apple M4, 2026-09-11)

Status: ROOT-CAUSED, not fixed. No product code changed by this record.

Tree: `43d10d3fc72` (`abacdaf4b9e` + `bc1582619e3` + F1 `74e083422a7` cherry-picked
onto `c84bee2021f`).
Binary: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`,
26264696 bytes, mtime 1788766698 (bracketed before and after; unchanged).
Run mode: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 ... run`.
Device reached: real Vulkan/MoltenVK, `device_identity=35079077912`, `handle=1`.

## Headline

**The GPU frame is pixel-EXACT. The mismatch is a length mismatch: the GPU route
returns an EMPTY framebuffer on every call after the first in a process.**

Measured, 900x760 = 684,000 px, `examples/06_io/ui/sample_web_renderer_sanity.html`:

| compare | mismatch_count | max_channel_delta | bbox |
|---|---|---|---|
| A `upload.readback` vs `upload.oracle` (software -> GPU upload -> readback) | **0** of 684000 | 0 | — |
| B `gpu.readback` (1st call) vs oracle | **0** of 684000 | 0 | — |
| C `gpu` 1st call vs 2nd call | **LENGTH 684000 vs 0** | — | — |

Per-call pixel counts in one process, GPU route called first so ordering cannot
be blamed: `call1 gpu_len=684000`, `call2 gpu_len=0`,
`receipt=source=cpu_fallback;skipped=0;ident=0;handle=0`.

`_web_draw_ir_pixels_equal`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:640-643`)
returns false on `left.len() != right.len()` before comparing a single pixel, so
`state.pixels_match` (`:989-993`) latches false at sample 2 and never recovers.
`web_gpu_paint_timing_evidence` then reports `reason=pixel-mismatch` — a correct
verdict with a misleading label. No primitive class diverges; classification by
Draw IR command (text / rect / rounded-rect / gradient / clip) is **not the
right question** and was not pursued once A and B came back exact.

## The actual failure, from `SIMPLE_VK_ORDER_TRACE=1`

```
[vk-order] readback-entry dirty=true ... cpu_fallback=false fb=1
[vk-order] flush rc=1 dirty=true cpu_fallback=false
call1 gpu_len=684000                      <- exact, device_readback, handle=1
[vk-order] flush rc=-1 dirty=true cpu_fallback=false          <- flush ERROR
[vk-order] dispatch pipe=1 batched=true rc=-1 fb=1 ...
[vk-order] cpu-fallback-first reason=framebuffer-dispatch-failed
call2 gpu_len=0                           <- cpu_fallback, ident=0, handle=0
[vk-order] dispatch-retry pipe=12 after flush rc=1
[vk-order] dispatch pipe=12 batched=true rc=0 fb=2 ...        <- fresh engine, still rc=0
[vk-order] cpu-fallback-first reason=framebuffer-dispatch-failed
[vk-order] dispatch pipe=23 batched=true rc=0 fb=3 ...        <- and again
```

Two distinct facts, both on the Simple side of the boundary:

1. **The first flush AFTER a successful readback errors (`rc=-1`) on the same
   framebuffer (`fb=1`).** `_dispatch_framebuffer_checked`
   (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:600-637`)
   takes the `dispatched < 0` arm at `:632`, calls `mark_cpu_fallback(
   "framebuffer-dispatch-failed")` (`:631`) and sets `completion_unknown`. The
   latch is sticky for the backend's lifetime
   (`backend_vulkan.spl:734-740`, `cpu_fallback_used`).
2. **In THIS workload, every Vulkan framebuffer created after the first is dead
   on arrival**: `fb=2` and `fb=3` fail their FIRST dispatch with `rc=0`, and
   fail it again after the one-shot fresh-command-buffer retry at
   `backend_vulkan_helpers.spl:612-618`. This is workload-specific, not a
   general Vulkan-backend defect — see the discriminating probe below. The
   engine-slot recovery path
   (`simple_web_layout_engine2d_fast.spl:282-310`: unhealthy slot ->
   `shutdown()` -> `Engine2D.create_with_backend_fast`) cannot recover — it
   manufactures a fresh dead engine per frame. This is the `engines_created`
   2 -> 3 step F1 observed in `vk1.txt` and left undiagnosed.

### Discriminating probe: the Vulkan backend itself is healthy

`build/perf/pixel_mismatch_2026-09-11/probe_twoengines.spl` creates two
`Engine2D.create_with_backend_fast(900, 760, "vulkan")` instances and does
`clear` + `draw_rect_filled` + `read_pixels_with_source()` on each:

```
engineA(first):            len=684000 source=device_readback ident=35313778712 handle=1
engineB(second, A alive):  len=684000 source=device_readback ident=35313778712 handle=2
engineA(again):            len=684000 source=device_readback ident=35313778712 handle=1
engineC(after A shutdown): len=684000 source=device_readback ident=35313778712 handle=3
```

So neither "framebuffer #2 cannot be allocated" nor "`shutdown()` poisons the
shared session" is true in general: concurrent engines, repeat use of an engine
after another's readback, and creation after a peer `shutdown()` all return a
live device readback. **The trigger is something the Draw IR page render does
that `clear`+`rect` does not** — candidates in order of suspicion: the glyph
atlas / text lane, the clip/scissor state folded into rect push constants
(`backend_vulkan_helpers.spl:619-624` warns about exactly this), and batched
command-buffer teardown across a readback.

Once (1) latches, `render.readback_source` becomes `cpu_fallback`,
`device_identity`/`backend_handle` drop to 0, and the Draw IR lane's readback
carries zero pixels — which is what `pixels_match` then sees.

## What it is NOT

- **Not arithmetic.** Zero differing pixels on a full 684,000-px page across the
  whole compare: no blend rounding, no coverage quantization, no half-pixel
  offset, no premultiplied-vs-straight alpha, no MoltenVK float-vs-int issue.
  Every per-channel histogram bucket (d=1, d=2, d=3-8, d>8) is 0 and
  `sum_dA=sum_dR=sum_dG=sum_dB=0`.
- **The upload leg matched, but its device provenance is NOT established.** In
  both probe runs the upload route was not the first Vulkan use of the process,
  so by the time it ran the engine had already latched `cpu_fallback`; on that
  path the presenter hands the host buffer straight back, which makes compare A
  identity by construction. `upload.readback.source` was not printed. Read A as
  "the round trip did not corrupt anything", not as proof of a sound
  device-side readback/swizzle/alpha path.
- **Not introduced by `bc1582619e3`** ("remove Vulkan mid-frame fences").
  `git revert --no-commit bc1582619e3` and re-running the probe reproduces
  identically: `call1 gpu_len=684000 / call2 gpu_len=0 / cpu_fallback`. The
  defect predates it.
- **Not a perf regression from F1 (`74e083422a7`).** One
  `examples/06_io/ui/web_render_page_ppm.spl` run at PAGE_W=900 PAGE_H=760 with
  `SIMPLE_2D_BACKEND=vulkan`: **20s** with F1, **21s** with the earlier F1 sha,
  against a 19.85s pre-F1 baseline. F1's "a single-render process renders only
  frame 0, so F1 cannot move this number" claim is confirmed, not assumed.
  `regression_source=none`.

## Fix (2026-09-11, same day)

**Both sub-fixes below were found to be one defect, and it was NOT where this
record predicted.** The suspects listed under "Recommendation" — glyph atlas,
clip-in-push-constant, batched teardown across a readback — were all eliminated
by an API-level bisection over five primitive classes
(`build/perf/pixel_mismatch_2026-09-11/probe_bisect.spl`): clear+rect,
+`present()`, +armed clip, clip left armed across the readback, and
`draw_text` via the atlas lane. **None reproduces it**; post-readback dispatch is
healthy in all five.

The real chain, and the fix, are recorded in
`doc/08_tracking/bug/vulkan_post_readback_dispatch_fails_latches_cpu_fallback_2026-09-11.md`.
In short:

- Sub-fix (2) of this record ("framebuffer #2+ never dispatches in this
  workload") was a **misreading**. The framebuffers are fine. One
  `vulkan_sffi_bind_pipeline` failure quarantines a command buffer the driver
  then refuses to discard, and because the reap verdict is
  `remaining.len() == 0 and orphan_remaining.len() == 0`, that one handle pinned
  `vulkan_sffi_reap_dependency_quarantine()` at false for the whole process.
  Every `_enqueue_framebuffer_compute` gates on that verdict, so every engine —
  new ones included — was shut out. Fixed by bounding the futile retries in both
  quarantine lists in `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`
  (which is pure Simple, not the Rust runtime).
- Sub-fix (1) ("why the post-readback flush returns -1") is still open at the
  driver boundary, but is no longer fatal: `_dispatch_framebuffer_checked` now
  re-syncs on `-1` and downgrades it to `0`, so `completion_unknown` is not
  raised and the readback returns pixels instead of nothing.

Measured on device, same binary, sanity page 900x760, 8 frames in one process:
`684000, 0, 684000(CPU), ...` (device abandoned permanently) -> **684000 on all
eight**.

The recommendation below to make the route report `device-lost` /
`zero-length-readback` instead of `pixel-mismatch` was **not** implemented and
remains open.

## Recommendation

One class, one fix — option **(b) make the GPU work**, since the GPU is already
proven reference-correct on frame 1. A tolerance (option c) would be actively
harmful here: the failing buffer is EMPTY, exactly the all-black/wrong-frame case
tolerance must never admit, and no tolerance can make length 0 equal length
684000 anyway. Option (a) is meaningless — the oracle already matches.

Two ordered sub-fixes, both in `src/lib/gc_async_mut/gpu/engine2d/`:

0. **Reproduce the latch with a minimal Draw IR composition** (bisect the sanity
   page by primitive class against `probe_twoengines.spl`'s clean baseline) to
   name the command that leaves the session unflushable. That bisect is the
   cheapest next step and was not run here.

1. **Find why the post-readback flush returns -1** on a framebuffer that just
   produced a correct frame (`backend_vulkan_helpers.spl:591-598`
   `_flush_for_host_fallback` / `_flush_pending_compute`). Likely a command
   buffer or fence left in a non-resettable state by the readback path
   (`backend_vulkan.spl:1613` `vulkan_sffi_readback_u32_into`).
2. **Find why framebuffer #2+ never dispatches in this workload** (`rc=0` on its
   first command, surviving the `:612-618` retry) even though a clean process
   allocates and uses three of them fine. Until this is fixed the sticky
   `cpu_fallback_used` latch is unrecoverable in-process even with a fresh
   `Engine2D`, so (2) is the load-bearing one: fixing it alone would let the
   existing slot-discard path recover.

Do **not** relax `pixels_match`, and do not special-case a zero-length readback
into a pass. A correct, cheap hardening that is not a tolerance: make the route
report `reason=device-lost` (or similar) when the GPU readback length is 0 or
`source != "device_readback"`, so this failure mode stops being mislabelled as a
pixel mismatch for the next investigator. The exact compare stays as-is.

## Artifacts

Probe (untracked, product-code seam reverted after the run):
`build/perf/pixel_mismatch_2026-09-11/probe_diff.spl` — calls the private
`_web_draw_ir_upload_route` / `_web_draw_ir_gpu_route` /
`_simple_web_layout_render_draw_ir_composition(.., "software", ..)` through four
temporary `pub` seams added to `simple_web_layout_engine2d_fast.spl` for the
investigation only.

- `build/perf/pixel_mismatch_2026-09-11/order_oracle.ppm` — software oracle, 900x760
- `build/perf/pixel_mismatch_2026-09-11/order_upload.ppm` — upload round-trip (identical to oracle)
- `build/perf/pixel_mismatch_2026-09-11/order_gpu.ppm` — GPU route, call 1 (identical to oracle)
- no `*_diff_A.ppm` / `*_diff_B.ppm` were written: both compares had zero differing pixels
- logs: `probe_order.log`, `probe_trace.log` (with `SIMPLE_VK_ORDER_TRACE=1`),
  `probe_norevfence.log` (fence commit reverted), `twoengines.log`
  (discriminating probe), `combined2.log` (20s timing run).
  `examples/06_io/ui/web_render_page_ppm.spl` prints no route/reason line — every
  route verdict quoted here comes from the probes, not from that driver.
