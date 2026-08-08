# wm_showcase 2D window refused an external frame slot (cap 4 vs 5 declared windows)

- **Date:** 2026-08-06
- **Status:** FIXED — 12/12 examples pass (was 6/12)
- **Spec:** `test/03_system/gui/wm_showcase_session_capture_spec.spl`
- **Signature:** `rejects=2d=external-frame-slot-refused`, `accepted=4` of 5,
  `rect_px=0 field_px=0`
- **Was hidden by:** the same spec's "no examples executed" false green
  (`doc/08_tracking/bug/wm_showcase_session_capture_spec_no_examples_executed_2026-08-06.md`).
  Fixing the vacuity with `slow_it` exposed this real defect underneath.

## Root cause

`src/os/compositor/host_compositor_core.spl:57`

```
val HOST_EXTERNAL_WEB_FRAME_MAX_COUNT: i64 = 4
```

caps the compositor's external content-frame slot table at **4** windows.
`src/app/wm_showcase/session.spl:111 wm_showcase_window_specs()` declares
**5** windows (gui, web, browser, terminal, 2d). The 2D window is fifth, so
`require_external_web_frame` (`host_compositor_core.spl:769`) hits its
capacity branch at line 775 and returns `false`;
`session.spl:455-458` then records `external-frame-slot-refused` and the
window is never composited.

### Proof it is the capacity branch, not the lookup branch

`require_external_web_frame` has exactly two refusal paths:

1. `window_id <= 0 or self._find_window_index(window_id) < 0` (line 770)
2. `self.external_web_window_ids.len() >= HOST_EXTERNAL_WEB_FRAME_MAX_COUNT`
   (line 775 `elif` falling through to line 781)

Path 1 is unreachable at the `session.spl:455` call site: the window was
created immediately above by `apply_wm_action("create_window")` and its id
read back from `self.comp.windows[index].id`, with `open_window` already
having returned early when `index < 0`. A refusal on a just-created window
can therefore only be path 2. `accepted=4` against a cap of exactly `4`,
with 2D fifth in the spec list, is an exact fit.

## When it broke

Commit `81f11d167d1` — *feat(wm-showcase): wire Simple Browser + Simple
Terminal windows (task #96)* — grew `wm_showcase_window_specs()` from
**3 to 5** entries (verified: `git show 81f11d167d1^:...| grep -c
"WmShowcaseWindowSpec("` = 3, after = 5) and updated the spec's expected
counts to 5/5/5. It did not raise the compositor's slot cap, which had
stood at 4 since the file's creation. Three windows fit under a cap of 4;
five do not.

The recently landed packed-UI-scene lane (`ui_gui_packed_producer.spl`,
`ui_web_packed_producer.spl`, `wm_packed_producer.spl`,
`ui_scene_event_route.spl`) and the browser `--open` change are **not**
implicated — the refusal happens at the slot gate, before any producer runs.

## All six failures are downstream of this one refusal

- `expected 4 to equal 5` — `accepted_frames`, the refused 2D window.
- `expected 0 to be greater than 0` on `rect_px`/`field_px` — the 2D frame
  was never accepted, so its palette never reached the composite. The
  producer palette is intact and matches the spec's pins exactly:
  `wm_full_stack_demo.spl:145` emits `0xffffa000` / `0xff15304a`, equal to
  the spec's `PROBE_2D_RECT` / `PROBE_2D_FIELD`. There is no second defect.
- `assert_true failed: got false` — `move_2d_scene` (`session.spl:503`)
  finds the recorded entry but its `set_external_web_frame` at line 527
  returns false for a window that owns no slot, so `scene_moved` is false.

## Fix

Two changes, both in `src/os/compositor/host_compositor_core.spl`.

### 1. Raise the ceiling (line 71): `4 -> 32`

Sized to match the sibling `HOST_EXTERNAL_CHILD_FRAME_MAX_COUNT = 32`.

The ceiling was kept rather than deleted, but it is now explained. The slot
arrays (`external_web_window_ids`, `external_web_frames`) are plain dynamic
arrays that are `push`ed, not preallocated — so this is **not** a fixed
buffer, DMA slot, or ABI limit. It survives only as a guard against
unbounded slot growth driven by content clients. Memory is bounded
separately and independently by `HOST_EXTERNAL_WEB_FRAME_MAX_PIXELS =
16777216`, checked per-set against the aggregate of every slot (line ~865),
so raising the count does not widen the memory envelope.

Headroom is deliberately well above the 5 windows in use, so the next added
showcase window does not reintroduce this defect.

### 2. Make the capacity refusal loud (line ~798)

The deeper defect is not the number — it is that exceeding the cap failed
**silently**, returning a bare `false`. That is how a 3->5 window growth
shipped without anyone noticing: an over-cap window presents as a window
that merely never draws. The capacity branch now logs, following the file's
existing `print "[hosted-wm] ..."` convention:

```
[hosted-wm] external-frame-slot-refused reason=capacity window_id={..} in_use={..} cap={..}
```

### Other consumers of the cap — checked, none

A repo-wide grep for `HOST_EXTERNAL_WEB_FRAME_MAX_COUNT` returns exactly
two hits: the definition and the single use at the capacity branch. Neither
`external_web_window_ids` nor `external_web_frames` is referenced outside
`host_compositor_core.spl`. Nothing assumed the value 4.

## Second defect, uncovered once the first was fixed

Fixing the slot cap took the spec from **6/12 to 10/12**. The two residual
failures were a *different* metric — `rendered_windows`, the count of
accepted windows whose content rect reads back byte-identically from the
composite (`session.spl capture()`):

```
✗ renders every declared window into the composited desktop
    expected 4 to equal 5
✗ changes the captured desktop when a window is closed
    expected 3 to equal 4
```

A diagnostic added at `session.spl` (see below) named the culprit directly:

```
wm_showcase_rect_unmatched 2d@20,320+240x90
```

### Root cause: the 2D window was occluded by the taskbar

The compositor draws the taskbar across the bottom `taskbar_height` rows of
the desktop — `taskbar_y = height - taskbar_h`, default 56
(`src/lib/common/ui/window_scene_draw_ir.spl:401-402`). With
`WM_SHOWCASE_DESKTOP_H = 430` the taskbar began at y=374, but the 2D window
spans y=288..414, so its lower band sat underneath the taskbar and could
never read back byte-identically.

The pixel receipts confirm the mechanism exactly: the 2D scene's rect
occupies y=344..372, entirely **above** y=374, which is why `rect_px=1344`
was perfectly intact (48x28 = 1344, the exact scene rect) while roughly
7,168 *field* pixels below y=374 were missing.

This is the same commit's second layout error. `81f11d167d1` grew the
desktop 360->430 to fit the new second window row, but 430 is not tall
enough once the taskbar's 56 rows are subtracted. It silently violated the
invariant `wm_showcase_window_specs()`'s own docstring asserts: *"Laid out
without overlap so each window's content rect can be read back unoccluded
from the composite."*

### Fix 3: `src/app/wm_showcase/session.spl` — desktop height 430 -> 480

Lowest row is the 2D window at y=288 h=126 (bottom edge 414), so the desktop
must be at least 414 + 56 = 470. 480 is used, leaving headroom.

### Fix 4: `src/app/wm_showcase/session.spl` — name unmatched rects

`capture()` now prints `wm_showcase_rect_unmatched <key>@<x>,<y>+<w>x<h>`
for any window that was *accepted* but does not read back byte-identically.
Same principle as the loud slot refusal: an accepted-but-unmatched window is
the interesting case (bad inset, occlusion, chrome offset) and a bare count
cannot be acted on. This diagnostic is what located the defect above.

## What was NOT done

No assertion was weakened, no example deleted or skipped, and no expected
value was adjusted. The spec's expectation of 5 accepted frames is correct
and was correct when `81f11d167d1` wrote it — the product simply could not
meet it.

## Files

- `src/os/compositor/host_compositor_core.spl:71` — ceiling raised 4 -> 32,
  with a comment stating why the ceiling exists and why memory is unaffected.
- `src/os/compositor/host_compositor_core.spl:798` — capacity refusal logged.
- `src/app/wm_showcase/session.spl:95` — desktop height 430 -> 480 so every
  window's content rect clears the taskbar.
- `src/app/wm_showcase/session.spl` (`capture()`) — unmatched content rects
  are now named rather than silently reducing a count.

## Verdicts (verbatim)

Command (direct path; the session daemon runs children under the debug Rust
seed and dies at 12s):

```
bin/simple test test/03_system/gui/wm_showcase_session_capture_spec.spl \
  --no-session-daemon --sequential --timeout 1800 --no-cache --no-cover-check
```

**Before** (baseline, slot cap 4):

```
wm_showcase_open declared=5 open=5 accepted=4 rejects=2d=external-frame-slot-refused
wm_showcase_palette rect_px=0 field_px=0
12 examples, 6 failures
```

**After slot-cap fix only** — 10/12, residual taskbar occlusion:

```
wm_showcase_open declared=5 open=5 accepted=5 rejects=
wm_showcase_palette rect_px=1344 field_px=13088
wm_showcase_rect_unmatched 2d@20,320+240x90
12 examples, 2 failures
Results: 12 total, 10 passed, 2 failed
```

**After both fixes** — 12/12:

```
wm_showcase_open declared=5 open=5 accepted=5 rejects=
wm_showcase_rendered rendered=5 declared=5 open=5
wm_showcase_palette rect_px=1344 field_px=20256
wm_showcase_palette_moved before=1344 after=1344
12 examples, 0 failures
Passed: 12
Failed: 0
Results: 12 total, 12 passed, 0 failed
```

The final numbers independently confirm the occlusion diagnosis:
`field_px = 20256` is exactly the predicted 21600 - 1344 (the full 240x90
scene minus its rect), where before it was 13088. And
`palette_moved before=1344 after=1344` is now area-preserving, as moving a
rect physically must be; the earlier `after=144` was the moved rect being
clipped by the taskbar.

## Both defects share one shape

Neither was a subtle algorithmic bug. Both were a **silently-swallowed
`false`**: a capacity refusal that returned a bare boolean, and a rect
mismatch that only decremented a counter. In each case the observable
symptom was "a window that simply never draws", which is why a 3->5 window
growth shipped twice-broken without anyone noticing — and why the false
green on top of it went unquestioned for so long. Both are now loud.
