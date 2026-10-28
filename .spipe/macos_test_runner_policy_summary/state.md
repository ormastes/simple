# macOS test-runner policy summary admission

Status: implemented; local shell self-test passes. Live admitted Phase 2 artifact
qualification was not run.

## Finding

`scripts/check/check-macos-test-runner-process-policy.shs` accepted any output
line containing `Results: ... 0 failed`. Consequently, a successful child that
executed zero tests and printed `Results: 0 total, 0 passed, 0 failed` could
satisfy the gate's green-summary condition. This is a real vacuous-admission
path in the macOS process-policy qualification gate.

The incidental `/private/tmp/mac_runner_false_green_probe` summary was not
reproduced as a test-runner defect: running its deliberate failing spec against
the current `origin/release/1.0.0` source via the existing Rust seed produced
`Results: 1 total, 0 passed, 1 failed` and exit 1. No broader false-green claim
is made from that earlier summary.

## Change

The gate now accepts a case only when its process exit code is zero and its
final canonical `Results:` line has the exact count format, canonical decimal
fields, a positive pass count equal to total, and zero failures. This gate
qualifies complete focused runs, so partial passes are rejected; skipped cases
are not accepted as a substitute for executed passes. If any `Results:` line is
present, the final one is authoritative; malformed or red final lines cannot
be hidden by an earlier green line. Legacy fallback formats are considered
only when there is no `Results:` line, and the last recognized fallback
summary is authoritative. The `--selftest-summary` mode covers these
precedence rules plus zero-result, all-skipped, malformed, leading-zero,
inconsistent-count, failing-summary, and contradictory exit cases.

The seven commands in the gate were run directly against the latest source
using the available Phase 1 `aa58` seed (no Phase 2 rebuild). All seven emitted
the canonical `Results: N total, N passed, 0 failed` format and returned 0 after
repairing the stale `args_spec.spl` expectation for retired JSON output. The
summary-format probe is not admitted Phase 2 artifact evidence.

The normal gate remains Darwin-only, requires the same admitted binary/hash and
host process baseline, and retains all seven original measured cases.

## Verification

- Baseline matcher reproduction: a green `Results:` line followed by
  `Results: 1 total, 0 passed, 1 failed` was accepted (`RED`).
- Baseline matcher reproduction: `Results: 0 total, 0 passed, 0 failed` was
  accepted (`RED`).
- `sh scripts/check/check-macos-test-runner-process-policy.shs
  --selftest-summary`: PASS.
- `sh -n scripts/check/check-macos-test-runner-process-policy.shs`: PASS.
- The seven focused command shapes each returned 0 and emitted a fully passing
  canonical `Results:` summary using the Phase 1 `aa58` seed.
- `test/01_unit/app/test_runner/args_spec.spl` passes 98/98 after aligning its
  JSON-format coverage with the current retired-option contract.
- `git diff --check`: PASS.

## Resume

Run the self-test with `sh scripts/check/check-macos-test-runner-process-policy.shs
--selftest-summary`. Run live qualification only with an admitted full CLI and
its independent SHA-256 receipt on macOS.
