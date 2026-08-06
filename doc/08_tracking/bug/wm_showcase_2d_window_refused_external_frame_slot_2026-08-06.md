# wm_showcase 2D window refused an external frame slot (cap 4 vs 5 declared windows)

- **Date:** 2026-08-06
- **Status:** FIXED
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

## What was NOT done

No assertion was weakened, no example deleted or skipped, and no expected
value was adjusted. The spec's expectation of 5 accepted frames is correct
and was correct when `81f11d167d1` wrote it — the product simply could not
meet it.

## Files

- `src/os/compositor/host_compositor_core.spl:71` — ceiling raised 4 -> 32,
  with a comment stating why the ceiling exists and why memory is unaffected.
- `src/os/compositor/host_compositor_core.spl:798` — capacity refusal logged.
