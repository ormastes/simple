# One failed `bind_pipeline` poisons the whole process: an unreapable dependency quarantine latches every Vulkan Engine2D onto the CPU fallback (Apple M4, 2026-09-11)

Status: ROOT-CAUSED and FIXED on device (three pure-Simple changes). The trigger itself — a refused `bind_pipeline` — remains open below the runtime boundary.

Supersedes the "framebuffer #2+ is dead on arrival" reading in
`web_draw_ir_gpu_route_pixel_mismatch_apple_m4_2026-09-11.md`. The framebuffers
are fine. The **process-wide dependency quarantine** is what is dead.

Binary: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`,
26264696 bytes, mtime 1788766698 (bracketed before and after every run below;
unchanged). Run mode:
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_VK_ORDER_TRACE=1 SIMPLE_2D_BACKEND=vulkan`.

## How it was found

The earlier record's suspects (glyph atlas, clip-in-push-constant, batched
teardown across a readback) were all **wrong**. An API-level bisection over the
primitive classes — `build/perf/pixel_mismatch_2026-09-11/probe_bisect.spl`,
five cases, each rendering twice on ONE engine with a readback in between:

| case | frame 1 content | call1 | call2 |
|---|---|---|---|
| A | clear + rect, no clip, no present | 684000 `device_readback` | 684000 `device_readback` |
| B | A + `present()` | 684000 `host_cache_after_device_copy` | 684000 same |
| C | B + `set_clip` armed around the rect | 684000 | 684000 |
| D | clip left ARMED across the readback | 684000 | 684000 |
| E | clear + `draw_text` (glyph atlas lane) | 684000 | 684000 |

**No primitive class reproduces it.** Post-readback dispatch is healthy in all
five. The trigger is not a primitive at all.

What found it instead was instrumenting every `-1`/`0` return in
`_flush_pending_compute_impl` and `_enqueue_framebuffer_compute` with the name
of the `vulkan_sffi_*` call that actually returned false, then running the real
route 8 times in one process
(`build/perf/pixel_mismatch_2026-09-11/probe_frames8.spl`, the sanity page at
900x760). Log: `frames8_before.log`.

## The chain, named

```
frame 1:
[vk-order] enqueue-fail stage=bind_chain pipe=12 desc=1 cmd=1 bind_pipeline=0 bind_desc=false push=false
[vk-order] flush-fail stage=end_compute cmd=1 pending_n=1 font_n=0
frame 2 and every frame after:
[vk-order] enqueue-fail stage=reap_dependency_quarantine pipe=45
[vk-order] enqueue-fail stage=reap_dependency_quarantine pipe=46
```

1. **`vulkan_sffi_bind_pipeline(cmd=1, pipe=12)` returns false — once.** This is
   the seed of everything. It is the FIRST link of the bind chain, so nothing
   downstream (`bind_descriptors`, `push_constants`, `dispatch`) was even
   attempted.
2. The bind-chain failure path calls `_flush_pending_compute()`, and
   **`vulkan_sffi_end_compute(cmd=1)` also fails** — the command buffer is
   already in an unrecordable state. The code then tries
   `vulkan_sffi_discard_command(cmd)`; when that also fails it calls
   `vulkan_sffi_quarantine_unsubmitted_command(...)` +
   `_quarantine_pending_compute_descriptors()` and returns `-1`
   (`backend_vulkan_helpers.spl:439-451`). That `-1` is what
   `_dispatch_framebuffer_checked` sees as `dispatched < 0`, and it latches
   `mark_cpu_fallback("framebuffer-dispatch-failed")` plus
   `completion_unknown` — for the backend's lifetime
   (`backend_vulkan.spl:734-740`).
3. **The quarantine then never drains.** From frame 2 onward, EVERY
   `_enqueue_framebuffer_compute` fails at its very first gate
   (`:496`, `vulkan_sffi_reap_dependency_quarantine()` returns false) and
   returns `0`, on every pipe, on every framebuffer, on **every Engine2D in the
   process** — including brand-new ones. That is why the earlier record saw
   `fb=2` and `fb=3` fail their first dispatch with `rc=0` and concluded
   "framebuffer #2+ is dead on arrival". The framebuffer is irrelevant; the
   gate is process-wide.

So the sticky `cpu_fallback_used` latch is not merely *sticky per backend* — the
engine-slot recovery path in
`simple_web_layout_engine2d_fast.spl:282-310` (discard the unhealthy slot,
`Engine2D.create_with_backend_fast` a fresh one) **cannot possibly work**, because
the fresh engine hits the same unreapable quarantine. It manufactures a fresh
dead engine per frame, exactly as observed.

### Device measurement, before the fix

`probe_frames8.spl`, 8 renders of the sanity page in one process:

```
frame 1: pixels=684000
frame 2: pixels=0            <- zero-length readback reaches the caller
frame 3..8: pixels=684000    <- CPU fallback, never the device again
```

Frame 2's `pixels=0` is the zero-length readback that
`_web_draw_ir_pixels_equal` (`simple_web_layout_engine2d_fast.spl:640-643`)
rejects on length, latching `state.pixels_match` false and mislabelling the
whole failure `reason=pixel-mismatch`.

## Where the boundary is

`vulkan_sffi_bind_pipeline` and `vulkan_sffi_reap_dependency_quarantine` are
runtime (`rt_vulkan_*`) calls. Why `bind_pipeline` fails once for `pipe=12`, and
why the quarantine can never be reaped afterwards, are both **below** the
pure-Simple boundary. See the `runtime_need` block recorded in
`.spipe/simple_2d_web_renderer_gpu_optimization/state.md`.

The pure-Simple side nonetheless owns three real defects, **all three fixed here**
(see "Fix"); the TRIGGER below the boundary is what remains open.

1. **A housekeeping failure is treated as a dispatch failure, permanently.**
   `_enqueue_framebuffer_compute:496` refuses to record ANY new work while the
   quarantine is unreapable. Reaping is best-effort GC of dead handles; a failed
   reap is a leak, not a reason to stop rendering forever on every engine.
2. **`framebuffer-dispatch-failed` is a lifetime latch with no retry on the
   `-1` arm.** The existing one-shot retry at `:612-618` fires only on
   `dispatched == 0`. The `-1` path — the one this incident takes — latches
   immediately, with no attempt to re-sync the device.
3. **A zero-length / non-device readback is reported as `pixel-mismatch`.** It
   is not a mismatch; it is an absence of evidence, and labelling it a mismatch
   sent the previous two investigations after the arithmetic.

## Fix

Three changes, all pure Simple, no runtime or seed edit.

**1. The quarantine can now drain — `sffi_vulkan.spl`.** Both quarantine lists
retried the same futile release forever, and the reap verdict is
`remaining.len() == 0 and orphan_remaining.len() == 0`, so ONE unreleasable
handle pinned it false for the process. Each list now spends a bounded budget
(`VULKAN_SFFI_ORPHAN_REAP_ATTEMPT_LIMIT` /
`VULKAN_SFFI_DEPENDENCY_REAP_ATTEMPT_LIMIT`, 3) and then ABANDONS what is left,
counting it (`vulkan_sffi_retired_orphan_command_count()`,
`vulkan_sffi_retired_dependency_count()`). Retiring leaks the handle — but the
previous behaviour leaked exactly the same handle AND stopped all rendering, so
this is strictly better, and the leak is counted rather than hidden. Device-idle
is already proven by the caller before any of this runs, so nothing in flight can
still refer to the abandoned handles.

Both lists had to be fixed: with only the orphan list bounded, the device still
showed `[vk-reap] complete=false deps=1 orphans=0 retired=1` on every remaining
frame — the dependency list alone kept the gate shut.

**2. A `-1` dispatch now re-syncs instead of latching —
`backend_vulkan_helpers.spl` `_dispatch_framebuffer_checked`.** The pre-existing
one-shot retry fired only on `dispatched == 0`; the `-1` arm this incident takes
had none. On `-1` the backend now proves idle (`vulkan_sffi_wait_idle()`), reaps,
and drops the wedged batch state. It re-enqueues **only when the dispatch had no
already-recorded siblings** (`pending_before == 0`): with siblings, the recovery
flush already destroyed the batch, so re-recording this primitive alone would
yield a frame missing the others while reporting success — strictly worse than
the fallback. With siblings the resync still runs (that is what unwedges the
session for the NEXT frame) and the frame fails over honestly. If `wait_idle`
fails, nothing is retried: that is genuine device-loss and still latches.

**3. After a resync, `-1` is downgraded to `0` on the RETURN VALUE.** The two
codes differ only in whether completion is KNOWN. After a proven-idle resync with
the command discarded unsubmitted, `0` ("it did not run") is truthful and `-1`
("it may have run") is not. This had to be done to the return value, not just to
`self.completion_unknown`: every caller in `backend_vulkan.spl:877-1043`
(`clear`, `draw_rect`, `draw_rect_filled`, rounded-rect, gradient) independently
re-applies `if dispatched < 0: self.completion_unknown = true`, so clearing the
field inside the helper alone was undone a few lines later in the caller — which
is exactly why the first two attempts at this fix still measured zero-length
readbacks. `completion_unknown` is what makes `read_pixels_with_source` bail at
entry and return `[]`; it **is** the zero-length readback.

### Device result

`probe_frames8.spl`, sanity page 900x760, same binary throughout
(26264696 bytes, mtime 1788766698, bracketed on every run):

| build | frames 1-8 pixel counts |
|---|---|
| before (`frames8_before.log`) | 684000, **0**, then 684000 on CPU fallback forever — device never used again |
| quarantine fix only, `-1` still latching (`frames8_diag3.log`) | 684000, **0**, 684000, **0**, 684000, **0**, 684000, **0** |
| all three (`frames8_after_clean.log`) | **684000 x8** |

The middle row is the discriminating intermediate: it shows the quarantine fix
alone restores recovery (no permanent demotion) but not the zero-length readback,
and the return-value downgrade alone would not drain the quarantine. Each fix is
load-bearing for a different symptom.

**4. The evidence label — `simple_web_layout_engine2d_fast.spl` /
`simple_web_html_engine2d_presenter.spl`.** A readback carrying no device pixels
is now CLASSIFIED before it is compared, by
`web_draw_ir_readback_absence(readback) -> text`: `"device-lost"` when the source
is not a device source (`cpu_fallback`, `completion_unknown`, `readback_failed`),
`"zero-length-readback"` when a backend still claims device provenance while
returning an empty buffer, `""` otherwise. Source is checked BEFORE length on
purpose — a backend that gave up usually also returns nothing, and calling that
`zero-length-readback` names the symptom instead of the cause.

The absence is threaded through `_WebDrawIrRouteState.readback_absence` (sticky,
first-wins, deliberately separate from `pixels_match`) into
`web_gpu_paint_timing_evidence`'s new trailing `readback_absence: text = ""`
parameter, which reports it as the reason ahead of `pixel-mismatch` and forces
`available` false. Both comparison sites are covered: the sampling path
(`:989-993`, which no longer calls `_web_draw_ir_pixels_equal` on an absent
sample) and the steady-frame path (`:927-933`).

**This is a classifier, not a tolerance.** Every non-empty absence refuses the
route exactly as a mismatch would; only the NAME changes. A zero-length readback
is still never a pass.

## Specs

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_readback_absence_label_spec.spl`
  — device-free, **12 examples, 0 failures** (seed
  `src/compiler_rust/target/bootstrap/simple run`). Pins the classifier on all
  six source/length combinations and the reason string, including the two cases
  that keep it discriminating: a genuine mismatch with a present readback still
  reports `pixel-mismatch`, and a clean faster sample still offloads. Writing it
  found a real ordering bug in the first draft of the classifier — a
  `cpu_fallback` with zero pixels was reported `zero-length-readback` instead of
  `device-lost` — which is now fixed and pinned.
- `test/05_perf/web_render_chrome/web_draw_ir_post_readback_dispatch_spec.spl`
  — device, **6 examples, 0 failures** on Apple M4. Six repeated page renders
  plus readback→dispatch cycles across rect / clipped-rect / text and an
  engine-teardown-with-surviving-successor case. **Read its "KNOWN WEAKNESS"
  section before trusting a green run** — see below.

### Sabotage

Reverting the single `dispatched = 0` downgrade line to a no-op and re-running:

| artifact | sabotaged | restored |
|---|---|---|
| `probe_frames8.spl` (`simple run`) | **RED** — 684000, **0**, 684000, **0**, ... | GREEN — 684000 x8 |
| the device spec above | **GREEN (did not discriminate)** | GREEN |

The probe gives a genuine green→red→green triple. The spec does **not**: under
the identical sabotage, binary, env, page and render call it still rendered six
full 684000-pixel frames, and a diagnostic print ruled out a vacuous guard (it
really rendered them). Something about the spec-runner process keeps the failing
path from being reached. This is recorded rather than hidden, and the spec
carries the same warning in its docstring.

## Still open

- **The device spec does not yet discriminate this fix** (above). Until the
  spec-runner/`run` divergence is understood, the probe is the evidence.

- **The trigger itself is unfixed and below the boundary.**
  `vulkan_sffi_bind_pipeline` still returns false on the first bind of each newly
  created engine (`pipe=12/45/78/111`, always `bind_pipeline=0` with the rest of
  the chain unattempted). That frame is now correctly demoted to the CPU fallback
  and returns a full-length buffer instead of nothing, but it is still not
  rendered on the GPU. Why MoltenVK refuses that bind is a `rt_vulkan_*`
  question.
- **Route authorization was not measured.** `probe_frames8.spl` drives
  `simple_web_render_html_to_pixels_with_engine2d_backend`, which never enters
  the Draw IR sampler at `simple_web_layout_engine2d_fast.spl:971-1022` —
  every frame reports `samples=0` and the default evidence from `:146`, with an
  empty comparison receipt, both before and after. So "the route becomes
  AUTHORIZED / `pixels_match=true`" is **not** demonstrated here; only the
  pixel-count oracle is. The gate that selects the sampling entry point has not
  been found.
- **The retry arm of fix 2 has never fired on device.** Every observed `-1`
  carried `pending_before=1`, so only the resync + downgrade were exercised;
  the `pending_before == 0` re-enqueue is unproven in the field.

## Artifacts

- `build/perf/pixel_mismatch_2026-09-11/probe_bisect.spl` — the five-case
  primitive-class bisection (all negative; retained because the negative result
  is what redirected the investigation).
- `build/perf/pixel_mismatch_2026-09-11/probe_frames8.spl` — 8-frame real-route
  probe; the reproduction and the before/after oracle.
- `build/perf/pixel_mismatch_2026-09-11/bisect.log`,
  `frames8_before.log`, `frames8_after.log`.
