# stage4 sspec gate reports capabilities it never exercised

- **Status:** OPEN (filed, deliberately not fixed in the documenting commit)
- **Date:** 2026-08-23
- **Script:** `scripts/check/check-post-bootstrap-stage4-sspec.shs`

## Symptom

The script ends with four unconditional `echo` lines:

```
post_bootstrap_stage4_test_runner=true
post_bootstrap_stage4_lint=true
post_bootstrap_stage4_duplicate_check=true
post_bootstrap_stage4_acceptance=true
```

Nothing in the script invokes a test runner, a linter, or a duplicate check. The
only work it actually performs is provenance canonicality (binary is a real
non-symlinked executable, provenance file adjacent, candidate provenance
verifies) plus a before/after hash of the essential-tools smoke log. The file's
own name promises an sspec run that never happens.

## Why this matters

It violates two corollaries of the phase-gating principle
(`doc/07_guide/tooling/bootstrap_phase_verification.md`):

- **A gate must name what it covered.** These lines name coverage that does not
  exist, which is worse than silence: a reader treats `..._test_runner=true` as
  evidence the stage4 binary ran tests.
- **A gate that examined zero items must report ERROR, never PASS.** Zero specs,
  zero lint findings and zero duplicate checks are examined, and the script exits
  0 having emitted four `=true` receipts.

## Why it is not fixed here

Deleting or conditioning those four lines changes what the gate enforces and
what downstream consumers of the receipt keys see. Per the standing rule, a doc
change must not quietly loosen or tighten a gate. The repair is its own reviewed
change.

## Repair sketch

Either (a) actually run the scoped stage4 prerequisite set on the stage4 binary
and emit the receipts from real results with counts, or (b) delete the three
unexercised receipt keys and rename the script to what it does verify
(`check-post-bootstrap-stage4-provenance.shs`), keeping `..._acceptance=true`
gated on the checks that genuinely ran. Either way the verdict line must carry
counts and scope per the principle.
