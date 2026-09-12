# Window Scene Draw IR Focused Spec Timeout — 2026-07-24

## Status

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
