# Stage 2 bootstrap sanity exits 2 without a diagnostic

Status: RESOLVED — 2026-08-20

The admitted Stage-4 bootstrap pipeline compiled and linked the Stage-2
bootstrap compiler successfully on x86_64 Linux with Cranelift:

- 666 compiled, 0 cached, 0 failed;
- 204.3 seconds compile plus 49.9 seconds link;
- output size approximately 25.5 MiB.

The immediately following bootstrap-compiler sanity command exited with status
2 and emitted no stderr/stdout line matching any diagnostic class. The canonical
stage diagnosis therefore reported `UNDIAGNOSABLE` and refused admission.

Evidence:

- `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`
- `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`
- planner admission cache key
  `1756465a130cd74a9bec274d06e4f70ea10c7d44a9cbd60ab4caf6d0a880fb33`

Resolution: the sanity gate expected stale version text
`simple-bootstrap 1.0.0-beta`; the canonical compiler reports
`simple-bootstrap 1.0.0-RC`. Both full-bootstrap and admitted-resume gates now
use the canonical value, and full-bootstrap emits a typed field summary on any
future sanity failure. Three subsequent Stage-2 candidates passed sanity and
advanced into Stage 3.

## Follow-up 2026-08-21 — the silence itself is now fixed and fenced

The 2026-08-20 resolution corrected the stale expected version string, but left
the *defect class* intact: `bootstrap_stage3_verify_sanity_evidence`
(`scripts/check/lib/bootstrap-stage3/sanity.shs`) failed via roughly thirty bare
`return 1` statements with no message, and its caller
`scripts/bootstrap/resume-stage3-from-admitted.sh` aborted under `set -eu` with
a bare `exit 1`/`exit 2`. Any *future* sanity failure of any other field would
therefore have been UNDIAGNOSABLE in exactly the same way — the version string
was the trigger, not the cause.

Fixed:

- every failure path in the verifier now emits
  `stage2-sanity-error: <field> mismatch ...: expected '<want>', got '<got>'`
  on stderr before returning non-zero;
- `resume-stage3-from-admitted.sh` exits 2 only through
  `bootstrap_stage3_error`, which prints
  `ERROR — nothing was checked (<reason>)` — exit 2 can no longer be bare and
  can never be mistaken for a pass.

Fenced by `scripts/bootstrap/check-stage2-sanity-diagnostic.shs --selftest`
(fatal, 7 fixtures). Each negative fixture asserts BOTH the non-zero exit AND
an actionable diagnostic naming the offending field — a non-zero exit alone is
explicitly not accepted, since every fixture already exited non-zero while the
bug was live. Proven fail-closed by replaying the gate against the pre-fix
library: `FAIL — 7 fixture(s) checked, stale-version:silent-failure
status-not-pass:silent-failure missing-field:silent-failure
candidate-sha:silent-failure frontend-sha:silent-failure
absent-evidence:silent-failure`. On the fixed library:
`PASS — 7 fixture(s) checked, every sanity failure emitted an actionable
diagnostic`.

### Wiring and the sibling self-test

`scripts/bootstrap/check-stage2-sanity-diagnostic.shs` is now wired into
`scripts/check/pre-push-conflict-tree-guard.shs` (declared, existence-swept
alongside the other guards so a missing file refuses the push rather than
passing blind, and invoked via `run_guard ... --selftest`). Full scan, not
range-bound: whether a gate can explain itself is a property of the scripts on
disk, not of the pushed range. `check-guard-wiring.shs` no longer lists it as
unwired.

`bootstrap_stage3_provenance_self_test` was initially reported here as
"independently broken, writes to /repo/...". That diagnosis was wrong and is
corrected: it always took a temporary root as `$1`, and run with one it exits 0.
The real defect was adjacent and of the same class — called with a missing or
relative root it silently resolved every path to an absolute `/repo/...` write
outside any temp root, failed, and returned non-zero with no explanation. It now
fails closed with `ERROR — nothing was checked (<reason>)` and returns 2 for a
missing, empty, relative, uncreatable, or unwritable root. Its sole caller
(`scri