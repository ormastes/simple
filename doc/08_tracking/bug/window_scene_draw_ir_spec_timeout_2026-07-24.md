# Window Scene Draw IR Focused Spec Timeout — 2026-07-24
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification 2026-11-25 (P3 fleet, release/1.0.0) — timeout STALE, one live failure remains (tracked elsewhere)

Ran the named spec on the tracked self-hosted bin/simple.exe at tree
fcd95d41d60:

```
SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl --mode=interpreter
```

Result: the file **completes in 42 s** (vs the 120 s file timeout on
2026-07-24) and now produces real assertion evidence: 12 examples executed,
11 passed, 1 failed. The timeout defect that is the subject of this record is
gone — no runner/profiling follow-up from this document is still applicable
(the 120 s timeout is not hit; nothing was raised or weakened).

The one failing example, "projects the window manager chrome and windows into
composed Draw IR batches" (`semantic: array index out of bounds: index is 0
but length is 0`), is a distinct, newly visible semantic failure in the same
scenario family already tracked by
`window_scene_draw_ir_spec_regressions_2026-08-26.md` (composed Draw IR batch
containment failure) — that record needs the semantic review it describes and
is NOT closed by this note. This record's timeout scope is done.

**Status:** RESOLVED for the timeout (spec completes with evidence in 42 s);
the residual example failure lives in
window_scene_draw_ir_spec_regressions_2026-08-26.md.
