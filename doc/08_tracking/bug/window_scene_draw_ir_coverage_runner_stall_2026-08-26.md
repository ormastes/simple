# Window-scene Draw IR coverage run stalls before closure

**Status:** OPEN (unverified 2026-09-12)

The combined coverage run for `window_scene_draw_ir.spl` made no progress for
more than four minutes and required termination (exit 143). Its partial CSV
contains runtime-hit decisions only and does not expose the complete static
denominator for the 1,765-line owner.

Required fix: split or instrument the owner so pixel storage, scene projection,
composition, and executor behavior have bounded measurable ownership; add a
native owner harness with explicit timeout/progress and static branch manifest.
Do not infer coverage from only the decisions emitted before termination.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
