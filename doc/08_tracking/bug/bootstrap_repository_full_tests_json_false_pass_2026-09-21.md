# Repository full-test inventory accepted ambiguous terminal JSON

- Date: 2026-09-21
- Severity: P1 (bootstrap verification false pass)
- Status: FIXED in source; focused macOS shell regression passes
- Provider: `scripts/bootstrap/bootstrap-phase-verification.shs`

`run_repository_full_tests` selected the last line beginning with
`{"success":` and extracted fields with `sed`. A zero-exit test runner could
therefore emit multiple terminal result rows or duplicate JSON object keys and
still be recorded as a passing Phase 3 or Phase 4 repository inventory row.

Repository rows now use `validate-test-runner-json.pl`, the same canonical
validator used by the focused compiler inventory. It requires exactly one
terminal row, parses JSON structurally, rejects duplicate structural keys,
checks the complete canonical key set and layout, and preserves status 91, 92,
and 93 for invalid, vacuous, and reported-failure results.

## Regression evidence

`test/01_unit/scripts/bootstrap_phase_command_owner_test.shs` runs one bounded
Stage 3 fixture with two hostile repository rows:

- `fixture_spec.spl` returns zero with duplicate outer `success` keys.
- `fixture_test.spl` returns zero after printing two valid terminal rows.

Against commit `6a7a22ddc37`, the added regression fails with
`duplicate-key repository row did not fail canonical validation`. With the fix,
both rows terminalize as `FAIL`, status 91, with zero executed examples, and the
complete command-owner fixture reports `bootstrap_phase_command_owner_test:
PASS` on macOS.

No bootstrap was run in this bounded lane.
