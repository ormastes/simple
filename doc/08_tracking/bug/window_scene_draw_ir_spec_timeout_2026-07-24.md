# Window Scene Draw IR Focused Spec Timeout — 2026-07-24

## Status

Open. The focused interpreter run of
`test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` timed out after
120 seconds while validating the WM glass-material projection.

## Evidence

- Runner: deployed Simple CLI with the Rust bootstrap driver, diagnostic only.
- Result: `0 passed; 1 failed`; file timeout at `120018ms`.
- Log: `build/wm-glass-window-material-diagnostic.log` (local, not committed).
- The run produced no assertion failure, so it does not establish whether the
  new material assertions pass or fail.

## Required Follow-up

Profile discovery/interpretation for this single spec with a fresh pure-Simple
product runner. Split the focused material scenarios into a smaller spec if
the existing broad file is the source of the timeout. Do not raise the timeout
or claim production evidence from the bootstrap driver.
