# Freestanding x86_64: WM material provenance loss chain — three stacked codegen corruptions

**Status:** layers 1–2 worked around (comparison hoisting, dimension threading);
layer 3 (page faults in the CPU glass composite) OPEN and now the rung-(d) blocker
**Date:** 2026-08-10
**Lane:** SimpleOS WM fullscreen evidence (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl` (`compute_styles_with_material`)

## Symptom
Rung-(d) blocker: every WM window degraded with
`[wm-frame] content-provenance-rejected ... fallback=none material=` and
`window-degraded reason=unresolved-or-duplicate-content`; `scanout_capture_size=0`,
all 4 PPMs missing.

## Actual field values feeding the decision (archived run 20260810T072511Z)
```
[web-style-producer] contract-attr index=4 ... raw_match=1 final_match=1
[web-style-producer] entry-rejected index=4 mode=engine2d-cpu-composited-material-v1
  bg=3424591649 gf=4294967295 gt=4294967295 layers_len=0 backdrop_len=25 animation=none
```
bg=0xCC1F1F21 (rgba(31,31,33,0.80) — translucent, correct), backdrop 25 chars =
`blur(30px) saturate(170%)` (admissible), layers empty, static. Every admission
conjunct is TRUE from these values — yet the entry was rejected.

## Root cause (plumbing, not renderer)
The material IS realized. The admission code compared the text locals
`wm_fallback` / `wm_material_mode` again ~120 lines after extraction (past the
font resolver and cascade calls). On the freestanding x86_64 lane the SAME
iteration printed `final_match=1` at extraction depth and then, in the next
build, took NEITHER the admitted NOR the rejected branch — the late `==`
evaluated false both times. Same defect class as the documented
`attr_value(...).trim().lower()` chained-dispatch corruption at the top of the
function; which comparison flips is build-layout dependent.

## Fix
Bind `wm_fallback_is_solid` / `wm_mode_is_cpu` / `wm_mode_is_empty` ONCE
immediately after attribute extraction and use the booleans in
`cpu_admitted` / `solid_admitted` / the rejection guard. Admission semantics
unchanged; the provenance validator
(`wm_content_frame_web_provenance_valid`, `src/lib/common/ui/window_scene.spl`)
was NOT touched. Verified: post-fix runs emit
`[web-style-producer] cpu-entries-ready count=1` and zero
`content-provenance-rejected` lines.

Also added a bounded `entry-rejected-detail` receipt printing every admission
conjunct, so a future rejection names its failing clause instead of forcing
inference.

## Layer 2 (fixed 2026-08-10): corrupt Engine2D dimension re-reads deep in the executor
With the admission witness restored, frames still carried `fallback=none`.
New receipts named the loss precisely (run 20260810T082051Z):
```
[web-material-provenance] witness-unconverted cpu_witness=1 cpu_executed=0 metal_executed=0 sha_len=64
[engine2d-glass] not-composited reason=bounds x=0 y=0 w=392 h=204 fb_w=49 fb_h=204
[engine2d-glass] not-composited reason=bounds x=0 y=0 w=452 h=264 fb_w=452 fb_h=33
```
`eng.width()`/`eng.height()` re-read inside
`_engine2d_draw_ir_render_glass_material` returned one garbage field per call
(49 for a 392px surface; 33 for a 264px one — the struct field-index-collision
class), so every correctly-sized full-surface material rect failed the bounds
check and `cpu_composited_material_count` stayed 0. Fixed by reading the
surface dimensions ONCE at `_engine2d_draw_ir_render_commands` entry and
threading them through `_engine2d_draw_ir_render_box` into the glass check
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`).

## Layer 3 (OPEN — current rung-(d) blocker): CPU glass composite page-faults
Run 20260810T083128Z (first run in which the composite actually executes):
8 recovering `[fault] *** EXCEPTION FRAME ***` at rip 0x8004bc0/0x8004bc2
(`rt_string_concat`) and 0x800434e/0x8004350 (`memcpy`), cr2 wild
(0x37b49f258, 0xffffffffffffff8c). The frame aborts; witness-unconverted with
`readback=` empty. Zero exception frames in every prior archived run — the
bounds corruption of layer 2 was masking this path entirely. This is a
freestanding codegen memory-corruption defect inside
`engine2d_draw_ir_glass_material_pixels` / its callers, not an evidence or
provenance issue. Needs its own reduction. **CONFIRMED STILL OPEN as of run
`20260810T112327Z`** (identical `rip=`/`cr2=` signature) — an earlier same-night
report that this was resolved was WRONG (that run had failed earlier, for a
different reason, and looked clean only because it never reached this path).

### Track W1 workaround attempted (2026-08-10, run `20260810T123139Z`) — FAILED, not a false lead but a wrong dependency assumption
Per `doc/03_plan/sys_test/simpleos_qemu_wm_real_screen.md` § "2026-08-10
rung-(d) minimum-path execution plan": added `_WM_CONTENT_FRAMES_ENABLED: bool
= false` (`src/os/desktop/shell.spl:99`) and gated
`self.runtime_content_frames(scene_revision)` in `render_baremetal_frame`
(`shell.spl:990-993`) to return `[]` when the flag is off, intending a
chrome-only first frame that skips the crashing paint entirely. Also flipped
`_WM_TRACE` to `true` for step localisation. Origin-sync precondition verified
first: fetched tip `a3b9ef4ec40`, confirmed `e99a5b76d11` (the
`closures_structs.rs` deep-field-copy fix) is an ancestor before building.

Gate run (`check-simpleos-wm-fullscreen-evidence.shs`) result:
`simpleos_wm_fullscreen_status=fail reason=guest-render-fault`,
`scanout_capture_size=0`, all four PPMs `missing` — did NOT reach rung (d).
Archived serial log (`build/simpleos_wm_fullscreen_evidence/runs/20260810T123139Z-fail/serial.log`,
297 lines, truncated with no fault frame and no `[wm-render-step]` trace lines
at all despite `_WM_TRACE=true`) shows the SAME
`web-style-producer`/`rfm`/`web-material-provenance witness-unconverted` →
5x `0x1dc020`-byte heap-alloc sequence that precedes the fault in the prior
`20260810T112327Z` run (compare lines 267-276 there), occurring during
`[desktop-gui] process-owned-surfaces-ready` / window materialize — i.e.
**before `render_baremetal_frame` is ever reached**. This falsifies the plan's
dependency note ("this track needs NO paint output at all... every window
takes the already-tolerated degraded branch"): the crash-triggering content
paint is NOT confined to the `runtime_content_frames` call gated by the new
flag — it also fires eagerly during window/surface materialization, on a path
this change does not touch. The flag and guard are implemented correctly per
the plan's steps 1-2 (lint-clean, default off, `runtime_content_frames` itself
untouched) but do not achieve the intended chrome-only degradation because the
paint call site assumed to be the only trigger is not the only trigger.
No check was weakened; `wm_content_frame_web_provenance_valid` and the gate
script are untouched. Root-causing the materialize-time paint trigger belongs
to Track W2 (root-cause, out of scope here) — this remains a DIAGNOSTIC run,
not a gate pass.

## Gap analysis — why nothing caught it
- AOT/freestanding-lane defects are invisible to the host spec corpus (known
  trap: host specs run interpreter/JIT, not the freestanding backend).
- The rejection path printed an aggregate line whose fields all looked valid —
  the receipt did not name the failing conjunct (now fixed).
- No enumeration was done for the family: any long function on the
  freestanding lane that re-compares a text local after many intervening calls
  is at risk. The compiler-level defect (text locals corrupted across call-rich
  regions / spill paths) needs its own reduction and fix; this doc is the
  tracking anchor.
