# SimpleOS WM: pointer-release render hangs forever in taskbar-tray text measurement (2026-07-26)

Status: OPEN — localized to one call, root cause not yet identified
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

## What must NOT be done to "fix" this

`need_render` is true merely because `pointer_sequence > 0`, so an ignored
pointer release re-renders an identical scene (same `scene_revision`, same
`taskbar_revision`). Suppressing that redundant render would make the frame
receipt print a valid generation and the evidence stage would pass immediately
— while leaving a render that never returns in the product. Any user dragging a
window hits this. The redundant-render question is worth raising on its own
merits, but it is NOT the fix for this bug and must not be used to turn the
gate green.
