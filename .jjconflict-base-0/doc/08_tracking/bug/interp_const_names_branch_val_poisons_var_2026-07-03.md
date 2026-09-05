# Interpreter: branch-scoped `val` const-poisons a later same-named `var` in the same function

- **Status:** FIXED (seed interpreter, `interpreter_helpers/patterns.rs`)
- **Date:** 2026-07-03
- **Severity:** high — aborted the whole chromed WM scene render lane
- **Component:** `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` (`bind_let_pattern_element`)

## Symptom

`error: semantic: cannot assign to const 'child_styles'` (exit 1) when rendering
any HTML where a flex container has both a `position:absolute` child and a
heightless stretch flex child — e.g. `shared_wm_scene_to_chromed_wm_scene`
(WM windows + taskbar). Scene `wm_scene_windows` of
`scripts/check/check-wm-gui-window-drawing-evidence.shs` crashed on it while
`wm_scene_css` passed.

## Root cause

`CONST_NAMES` is a thread-local `HashSet<String>` with **function lifetime and
no block scoping** (saved/cleared/restored only on function entry/exit). Inside
one function invocation:

1. a branch executes `val child_styles = ...` → name inserted into `CONST_NAMES`;
2. a sibling scope later executes `var child_styles = ...` → env re-bound, but
   the stale `CONST_NAMES` entry was **not removed**;
3. the following `child_styles = ...` assignment hits the const check and aborts.

In the renderer this is `layout()`: the absolute-child branch declares
`val child_styles` (~line 6974) and the flex main loop declares
`var child_styles` (~7036) then reassigns it in the align-stretch branch (~7087).
Only inputs that execute *both* paths in one call crash — which is why small
fixtures passed and the WM chrome scene didn't.

## Fix

In `bind_let_pattern_element`, a mutable binding now removes the name from
`CONST_NAMES` (both `Pattern::Identifier` with `is_mutable` and
`Pattern::MutIdentifier`). Mirrors the existing module-global exception added
for the `arm_body` case.

## Repro / verification

- Probe: flex row (`position:relative`, fixed height) + `position:absolute`
  child + heightless `flex:1` child → `simple_web_layout_render_html_software_pixels`.
  Before: semantic abort. After: renders (19200 px @160x120).
- Negative: `val x = 1; x = 2` still errors "cannot assign to const 'x'".
- Shadow: `if true: val y = 1` then function-level `var y = 5; y = 9` works.
