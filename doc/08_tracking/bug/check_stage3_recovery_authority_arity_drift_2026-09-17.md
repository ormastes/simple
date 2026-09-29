# `check-stage3-recovery-authority.shs` arity drift makes the Stage 3 recovery preflight refuse `stage2-admission-invalid` unconditionally

- Status: OPEN (2026-09-17) — found by the phase-1a live-bug lane (windows_bootstrap_cmp_authority_missing); recorded, not fixed (separate ownership from that lane)
- Found: 2026-09-17
- Component: `scripts/bootstrap/check-stage3-recovery-authority.shs`, `test/01_unit/scripts/stage3_recovery_authority_guard_test.shs`
- Binary: n/a (check-script defect)

## Observation

`check-stage3-recovery-authority.shs` calls `bootstrap_stage3_verify_stage2_admission_receipt` with **9 arguments**, but the signature at origin/main takes **21**. The arity mismatch makes the Stage 3 recovery preflight refuse the `stage2-admission-invalid` scenario unconditionally, regardless of the receipt's actual validity.

Two follow-on defects ride on the same drift:

1. The script's 6 provenance gates still use bare `cmp -s` — the exact defect class fixed for the main bootstrap path by `bootstrap_stage3_compare_bind`/`compare_files` (`authority.shs`), currently unreachable because the preflight dies first.
2. `test/01_unit/scripts/stage3_recovery_authority_guard_test.shs` carries the same stale 9-arg fixture (`bootstrap_stage3_write_stage2_admission_receipt`), so the guard spec dies in setup before running any assertion.

## Fix direction

- Align the call and the guard-test fixture with the 21-arg receipt signature.
- Convert the 6 provenance gates to the bound comparator (`bootstrap_stage3_compare_files`) the same way the main bootstrap path was fixed.
- Evidence required: the guard spec's literal PASS/`Results:` line, plus a negative case proving `stage2-admission-invalid` is accepted when the receipt is genuinely invalid.

## Related

- `doc/08_tracking/bug/windows_bootstrap_cmp_authority_missing.md` (the fixed main-path comparator defect this drift was found beside)
