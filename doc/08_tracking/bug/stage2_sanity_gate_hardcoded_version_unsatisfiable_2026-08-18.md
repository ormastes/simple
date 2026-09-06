# Stage-2 sanity gate was unsatisfiable: hardcoded version literal, hidden by a copied receipt

- **Date:** 2026-08-18
- **Status:** FIXED
- **Severity:** blocker (Stage 3 and Stage 4 could not be reached)
- **Files:** `scripts/bootstrap/bootstrap-from-scratch.sh` (`bootstrap_stage_sanity()`),
  `scripts/check/check-bootstrap-stage2-sanity-gate.shs` (new test)

## Symptom

A full `--full-bootstrap` built Stage 2 successfully (`664 compiled, 0 cached,
0 failed`, linked 128361 KB, 360.5s) and then failed its post-build sanity gate
with `exit 2` and **no diagnostic text at all**. The failure path ran
`rm -f "${stage2_bin}"`, destroying the artifact it had just spent ~6 minutes
building.

## Root cause

`bootstrap_stage_sanity()` compared the candidate's `--version` output against a
**hardcoded literal**:

```sh
[ "${version}" = "simple-bootstrap 1.0.0-beta" ] &&
```

Release commit `9a3f6051996 release: 1.0.0-RC` bumped
`src/app/cli/bootstrap_identity.spl` (and `./VERSION`) from `1.0.0-beta` to
`1.0.0-RC` and did not update this literal. From that commit onward the gate was
**unsatisfiable by any correctly-built Stage-2 binary**.

Confirmed from the run's own evidence
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-sanity.env`):
`version_output=simple-bootstrap 1.0.0-RC`, every recorded `*_status` field `0`
except `unsupported_status=1` — **which is the value the gate requires**.

## Two things that made this expensive to find

1. **The version comparison had no `*_status` field in the evidence.** Every
   recorded field read as passing while the gate returned failure. The one
   discriminator that actually failed was the only one not recorded.

2. **A misreading the evidence actively invited.** `unsupported_status=1` looks
   like a failure but is the *required* value: the `run` sub-check is a
   **negative control**, asserting that a bootstrap-entry candidate *rejects*
   `run`. It passed byte-for-byte —
   `printf '%s' "error: unknown command 'run'" | sha256sum` reproduces
   `373ffddd775f9bc524eb271bab164edcd7a51209a53058465cd0538c50c8d806`, exactly
   the `unsupported_output_sha256` in the evidence. The initial diagnosis of
   this bug wrongly concluded the `run` check was unsatisfiable by construction
   and nearly removed a working control.

## Concealment defect (tracked separately here, by request)

The imported Stage-2's `stage2-sanity.receipt` states verbatim `note: sanity
evidence is COPIED, not re-measured in this tree.` and carries only
`version_status` and `frontend_smoke_status` — certified under an older schema.
Because it was copied rather than re-measured, the first honest evaluation of
this gate in this tree was also the first time the stale literal could bite.
**A copied receipt is not evidence.** For an unknown period the gate was
reported green without ever having been run.

## Fix

- Expected version is **derived** from `./VERSION`, never hardcoded.
- `./VERSION` is **cross-checked** against `src/app/cli/bootstrap_identity.spl`;
  drift between the two — the exact defect here — is `status=error`.
- Fail-closed: unreadable/empty `VERSION` is `error`, never a pass. Evidence
  gains `checks_run`; a run that evaluated nothing cannot read as a pass.
- New evidence fields `version_expected`, `version_expect_status`,
  `version_match_status`, `unsupported_match_status`, `sha_stable_status`.
- Every failing sub-check now **prints a named diagnostic** instead of a silent
  `exit 2`.
- The rejected binary is preserved as `${stage2_bin}.rejected` instead of being
  deleted, retaining post-mortem value while still keeping it off the
  downstream `-x "${stage2_bin}"` guards (which is all the delete achieved).
- The `run` negative control is **unchanged**, and is now commented so it is not
  mistaken for a capability probe again.

## Test

`sh scripts/check/check-bootstrap-stage2-sanity-gate.shs` — verdict is the last
stdout line (`PASS`/`FAIL`/`ERROR`); 0 cases is `ERROR`. It extracts
`bootstrap_stage_sanity()` from the shipped script at run time, so it cannot
drift from the code it certifies, and refuses to run at all if the gate ever
reacquires a hardcoded version literal.

12 cases: the reproducer (current repo version must be accepted), five
must-still-reject cases (wrong version; frontend smoke broken — the 2026-08-09
can't-lex-two-lines shape; dead stub exiting non-zero; a candidate that
*accepts* `run`; missing `VERSION`), the VERSION-vs-identity drift case, and
five evidence-completeness assertions.

**Negative control (measured, rc read on the line after the command):** with the
fix reverted the suite is `FAIL` rc=1 with `reproducer_current_version: FAIL
(expected accept; rc=1 status=fail)`; with the fix applied it is `PASS` rc=0.
All five reject cases reject under **both** gates — the fix did not blind it.
