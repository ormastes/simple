# String unit suffix used byte length for scalar advancement

**Status:** OPEN (unverified 2026-09-12)

`scan_string_unit_suffix` collected a Unicode suffix into `String`, then looped
over `suffix.len()` while `advance()` moves one Unicode scalar. A suffix such as
`_한글` therefore advanced six times for three scalars and could consume later
tokens or reach EOF incorrectly.

The implementation now uses `suffix.chars().count()` for the minimum-length
check and consumption count. A focused regression fixture verifies a typed
Unicode suffix followed by another identifier, but its test lane reached the
three-cycle cap before a clean rerun. Keep this defect open until that fixture
and branch coverage pass in a fresh session.


## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
