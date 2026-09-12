# Window-scene Draw IR specification regressions

**Status:** OPEN (unverified 2026-09-12)

The 2026-08-26 combined coverage attempt completed 60 scenarios and failed 3:

- readable-bitmap selected-metrics source assertion;
- composed Draw IR batch containment assertion (`expected 12 to contain ,`);
- no-snapshot legacy rectangle hash mismatch (`4292668155` expected
  `4293059302`).

The failures need semantic review before changing goldens. In particular, the
hash must be updated only if the changed byte stream is intentional and the
canonical Draw IR/device evidence remains equivalent.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
