# SimpleOS WM: pointer-release render hangs forever in taskbar-tray text measurement (2026-07-26)

Status: UNVERIFIED — an unretained local x86 fullscreen run reportedly passed;
the latest canonical tracked report is FAIL, and ARM/SIMD remain unverified

## Local rerun53 observation (2026-07-26; not retained evidence)

An unretained local x86 fullscreen-wrapper run was reported with
`status=pass reason=pass`, zero production faults, `changed_bytes=23054033`,
and `restored_sha256 == baseline_sha256` byte for byte (the screen reportedly
returned exactly to its pre-maximize state), with the font region still
matching its pinned oracle.

That observation is useful for directing the next rerun, but it is not
acceptance evidence. No rerun53 report, capture artifacts, artifact hashes, or
build/runtime attestation were committed, so the result cannot be reproduced
or independently verified from this repository. It proves neither the ARM
QEMU lane nor the required x86/ARM SIMD receipts.

The latest canonical tracked report remains
`doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-24.md`, which records
`status: fail` and `reason: wm-simple-web-build-failed`. Therefore the
SimpleOS-WM x QEMU lane must remain unverified until a fresh canonical run
retains its report, captures, hashes, provenance/attestation, and applicable
SIMD receipts.

The local timing improvement was associated with **memoizing the font asset
catalog** (cf09420b88e). `selected_font_asset_candidates()` rebuilt 16 structs
from long string literals on every call, and the by-path lookup calls it more
than once per invocation, so a single frame rebuilt that catalog hundreds of
times. In the reported local run, removing that repeated work allowed the
release render to finish inside the correlation budget.

**Be precise about what the local observation suggests: the render got fast
enough in that run; it does not establish a canonical lane PASS.** The moving
stall point across builds remains evidence against a fixed infinite loop and
supports pathological slowness as the working diagnosis.

### Still open, and NOT fixed by this

`has_ttf=0` on **117 of 118** metric resolves, including on cache hits. Nearly
all WM text is still drawn by the legacy bitmap fallback rather than real font
metrics; exactly one real font load succeeded in the whole reported session.
The unretained local run reportedly completed because the frame finished in
time, not because the font pipeline was healthy. That anomaly deserves its own
investigation — see "The actual anomaly" below.

Also unfixed and unaffected: the resolved-metric cache reading `keys=0
values=0` (side finding below).

---

Original report follows.

Status when filed: OPEN — localized to one call, root cause not yet identified
Lane: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (SimpleOS-WM x QEMU showcase cell)

## Symptom

The pointer RELEASE step never produces its frame receipt. The guest goes
completely silent — no panic, no fault, no reset, empty `qemu.out`, and not
even a heap allocation — and stays silent indefinitely (confirmed at a 300s
budget: serial log's last write was exactly 300s before the harness gave up).

The harness fails with
`guest-pointer-irq-state-frame-correlation-missing kind_code=2`, verdict
`capture-input-or-guest-correlation-failed`.

Everything up to that point is green: press correlation
(`command=window_drag_begin target=3 handled=true`), all three PPM captures,
three windows' material digests, and the pinned font-region oracle.

## Where it hangs (bisected by receipts, 8 rerun cycles)

```
shell run_baremetal loop
  [wm-loop-step] at=before-render need_render=1          <- reached
  render_baremetal_frame
    [wm-render-step] at=content-frames                   <- reached (web raster DONE)
    [wm-render-step] at=executor-render                  <- reached
    Engine2dWmFrameExecutor.render
      [wm-exec] at=window-loop-end images=3 degraded=0   <- reached, all clean
      [wm-exec] at=composition-begin                     <- reached
      shared_wm_scene_draw_ir_composition_with_content
        [wm-comp] at=base-begin                          <- reached
        shared_wm_scene_draw_ir_composition
          [wm-base] at=taskbar-objects-batch             <- reached
          _wm_draw_ir_taskbar_objects_batch
            [wm-tbar] at=objects-done object_index=6 commands=12   <- reached
            tray loop, tray.len()==1, ONE iteration:
              [wm-tbar] at=tray-item index=0 item_len=5 label_len=5 <- reached
              [wm-tbar] at=tray-rect x=3728 y=2112 w=56 h=48        <- reached
              [wm-tbar] at=tray-rect-pushed                         <- reached
              _wm_draw_ir_text -> resolve_font_metrics_with_language  <- NEVER RETURNS
```

## The decisive counts

```
tray-item=7  tray-rect-pushed=7  tray-text-pushed=6  tray-done=6
```

Seven tray iterations entered, seven rects pushed, only **six** texts
completed. Every iteration logged byte-identical inputs
(`index=0 item_len=5 label_len=5`) and a sane rect. So the same call with the
same input succeeded six times and hung the seventh.

**This is state accumulation across compositions, not bad input.**

## Hypotheses ELIMINATED (each by evidence, not argument)

| # | Hypothesis | Killed by |
|---|---|---|
| 1 | Corrupted / unterminated `tray.label` | `label_len=5`, and six identical successes first |
| 2 | Garbage-huge taskbar collection length | `pinned=3 running=3 tray=1 scene=3840x2160` |
| 3 | Exponential nested-content recursion | `recurse parent='3' depth=1 frames=3`, healthy |
| 4 | `WM_CONTENT_FRAME_MAX_NESTING_DEPTH` initializer never ran | printed `cap=3` |
| 5 | Slow 4K render, budget too small | 300s of ZERO output; a slow render still emits receipts and heap traffic |
| 6 | Web render budget floor causing a spin | every `_web_budget_expired()` guard EXITS its loop; the floor only permits work |
| 7 | Facade mutex deadlock | `_font_mutex_acquire` skips lock/unlock entirely when `_registered_selected_fonts_only`; and the filed defect for those locks faults rather than hangs |
| 8 | Window ordering / `visible_windows_by_layer` | returned `layer_windows=3` and completed |

## Precise failure point

Caller-side receipts (rerun49/50) pin it to a single call:

```
[wm-text] at=begin id=taskbar-tray-label-clock value_len=5
[wm-text] at=candidate
[wm-text] at=resolve family=Noto Sans Mono      <- last line, forever
```

Counts across a whole session: **begin=76, resolve=76, resolved=75.** All 76
calls use the same family. So the 76th `resolve_font_metrics_with_language`
never returns; 75 identical-shaped calls before it did. The failing one happens
to be the tray clock label only because that is the 76th text drawn.

## Remaining suspects (inside `resolve_font_metrics_with_language`)

1. `_resolved_font_metric_cached`'s scan is bounded by a **module-global
   array's `.len()`**, and array-typed module globals are a documented broken
   channel here. (Weakened: the one watchdog reading that length reported
   `keys=0 values=0`, i.e. an empty array and a trivial scan — see side finding.)
2. `renderer.measure_text_advances(content, font_size)` and the glyph
   rasterization/atlas path beneath it. This is now the leading suspect: it is
   the only remaining unmeasured heavy step, it owns the state that accumulates
   across calls (glyph cache, atlas — `FontRenderer._reset_font_atlas` was seen
   allocating 1M elements twice), and it is where the separately filed
   `font_renderer_glyph_loop_heap_corruption_segv_2026-07-20.md` also lives.

### ELIMINATED: `GlyphCache.insert` eviction loop (was suspect 2)

The old loop used `self.entries`/`self.payload_bytes` as both its bound and its
mutation target, so it terminated only if those method-receiver writes
committed — a perfect fit for the copy-commit landmine, and the call count (76)
lands exactly where ~75 labels first fill `max_entries=512` and make the loop
run at all. It was rewritten to count on locals and apply one bulk slice
(6b7451f319a), making it structurally unable to spin.

**The hang did not move: still begin=76, resolved=75, same call.** So this loop
was never the cause. The rewrite is kept on its own merits — it removes an
unbounded loop and an O(N^2) slice path from a kernel hot loop, and is verified
by `probes/dg_glyph_cache_evict.spl`.

## CRITICAL: probing inside font_renderer.spl REGRESSES the lane

Adding `print` receipts inside `_resolved_font_metric_cached` (commit
464b2e1450a) caused rerun48 to regress hard: `frame-degraded skipped=1 ...
text-font-batch` came back — the exact defect the C5 enum-match fix had closed
— and the run captured **no PPMs at all**, verdict `guest-render-fault`. Boot
was clean, so the probe itself was the cause: this region is layout-sensitive
and inserting code flips a miscompile.

**Instrument from the CALLER (`_wm_draw_ir_text` in window_scene_draw_ir.spl),
never from inside font_renderer.spl.** The revert is 81d8d41e68f.

## rerun51: it is SLOWNESS, not a fixed infinite loop — and the font is unavailable

Phase receipts inside the resolver changed the picture twice over.

**1. The stall MOVES between builds.** rerun50 stopped inside
`resolve_font_metrics_with_language`; rerun51 stopped one step earlier, inside
`simpleos_default_font_asset_candidate()` (`begin=76, candidate=75`). Same 76th
call, different sub-step. A fixed infinite loop does not relocate when
unrelated code is added — this is the deadline landing wherever the guest
happens to be, i.e. pathological SLOWNESS. The earlier "300s of total silence"
is consistent: a single slow call emits nothing for its whole duration.

**2. The font is unavailable for essentially every text.** Counts across one
session:

```
rfm: default-font=118  renderer-bound=118  cache-lookup=1  measure=1  measured=1
wm-text at=resolved:   valid=0 x74,  valid=1 x1
```

117 of 118 resolves return early at `if not renderer.has_sffi_ttf()` with
`reason="font-runtime-unavailable"`, so nearly all WM text is drawn by the
legacy bitmap fallback (`draw_ir_text`) rather than real font metrics. Exactly
one real measurement happened in the entire run — and it completed.

## REFUTED: "module-global caches do not persist" (rerun52)

The direct measurement killed it. `from_cache` / `has_ttf` across one session:

```
  74  from_cache=1 has_ttf=0     <- cache HIT, cached renderer has no font
  43  from_cache=0 has_ttf=0     <- miss, freshly loaded renderer also has no font
   1  from_cache=0 has_ttf=1     <- the single successful font load
```

The loaded-face module-global cache **does** persist and serve — 74 hits. So
there is no per-text re-parse of a 17MB face, and the "every node reloads the
font" cost model below is wrong. Retained here as a corrected record rather
than deleted, because it was reasoned from two real observations (`keys=0
values=0`, `has_sffi_ttf()` false) and both were consistent with it.

## The actual anomaly: the font never loads

`has_ttf=0` on **117 of 118** resolves — including on cache hits, which means
the cache is faithfully caching a renderer that carries no font. Exactly one
load in the whole session succeeded. Consequences:

- Nearly all WM text is drawn by the legacy bitmap fallback, not real metrics.
- Those 117 calls return EARLY and are therefore CHEAP, so the "resolve path is
  slow" story does not hold either — the stall is not explained by work done in
  the resolver.

Why the face fails to load is now the open question, and it is well-defined and
independent of the pointer-release stall. It is also a product-quality defect in
its own right: the desktop is rendering essentially all of its text without the
font it reports using.

## Old (superseded) cost model: module-global caches do not persist

Three independent observations point at one defect:

- `_resolved_font_metric_keys` / `_resolved_font_metric_values` read `keys=0
  values=0` after many stores (see side finding below).
- `has_sffi_ttf()` is false on 117/118 calls, i.e. the loaded-face cache
  (`_browser_default_font_families` / `_browser_default_font_renderers`) is not
  serving anything either.
- Both are **module-global arrays**, and array-typed module globals are a
  documented broken channel here — `.push()` writes degrade and do not persist
  (see the project memory entry for module-global MIR lowering: array globals
  were fixed for the same-module case, cross-import globals are still broken).

If those caches never persist, then per the comment above
`_browser_default_font_families`, **every single text node re-attempts a real
dlopen + TTF parse of a 17MB face** — "quadratic for a real page and the
dominant web-render cost under the interpreter", by that comment's own
admission. That is more than enough to push one WM frame past 300s under TCG,
and it explains why the stall lands at a different sub-step each build.

This root cause sits in the COMPILER (module-global lowering), whose campaign is
parked under the standing no-bootstrap-unless-essential rule. It is not fixable
from the WM/font side.

## Side finding: the resolved-metric cache never populates

The one watchdog line that did print before the revert read:

```
[rfm-scan] lengths keys=0 values=0 limit=128
```

Both module-global cache arrays were EMPTY, so `_resolved_font_metric_store`'s
`.push()` is not persisting and every text re-resolves from scratch. Consistent
with array-typed module-global writes degrading on this lane. It is NOT the
hang (an empty cache makes the scan trivial), but it is a real and expensive
perf defect — the cache exists precisely because re-resolving is the dominant
render cost.

## Stall point is build-dependent (layout-sensitive), stable within a build

| run | stops at |
|---|---|
| rerun50 | past `at=candidate` and `at=resolve`, inside the resolver |
| rerun51 | `at=begin` — inside `simpleos_default_font_asset_candidate()` |
| rerun52 | `at=begin` — same as rerun51 (same build shape) |

Always the **76th** `_wm_draw_ir_text` call, but the sub-step moves when
unrelated code is added. Same layout sensitivity that made probing inside
font_renderer.spl regress the lane outright. Any future attribution must
account for this: a single run's stop line names a symptom position, not the
defect.

Worth noting for whoever picks this up: `simpleos_default_font_asset_candidate()`
rebuilds the entire 16-entry candidate catalog on EVERY call — each entry
constructed with several long string literals (copyright, table list, subsets,
sha256 hex) — and the lookup path calls that builder more than once per
invocation. It is called once per text draw. That is a genuine and easily fixed
inefficiency (hoist to a cached catalog) regardless of whether it is this stall.

## What must NOT be done to "fix" this

`need_render` is true merely because `pointer_sequence > 0`, so an ignored
pointer release re-renders an identical scene (same `scene_revision`, same
`taskbar_revision`). Suppressing that redundant render would make the frame
receipt print a valid generation and the evidence stage would pass immediately
— while leaving a render that never returns in the product. Any user dragging a
window hits this. The redundant-render question is worth raising on its own
merits, but it is NOT the fix for this bug and must not be used to turn the
gate green.
