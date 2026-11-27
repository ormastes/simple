# Simple lint silently accepted unknown options — 2026-07-23
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** RESOLVED 2026-11-25 — source fix verified present by code
inspection (see dated verification note below); the pure-Simple Stage 4 CLI
qualification run remains pending and environment-blocked, but the defect
described here is fixed in source.

## Reproduction

`simple lint test/fixtures/lint/clean.spl --bogus`, bare `--profile`, and empty
`--profile=` continued into normal linting. A clean file could therefore exit 0
even though the invocation was invalid.

## Root cause and fix

The public wrapper collected known wrapper flags and file paths but ignored all
other dash-prefixed arguments. The compiler lint owner only inspected flags it
understood, so neither layer rejected the typo.

The wrapper now validates its closed supported option set before file work and
returns usage exit 2 with human or JSON error output. The focused contract
covers unknown, bare-profile, empty-profile, and JSON unknown-option cases.

A fresh pure-Simple Stage 4 CLI must run the focused contract and public lint
smoke before qualification.


## Verification 2026-11-25 (work/p2w5-ai-20261125)

**Classification: STALE-CLOSED (source fix confirmed present; executable
qualification environment-blocked).**

Code inspection on release/1.0.0 confirms the fix is real and in place:

- `src/app/io/cli_lint_commands.spl:309-317` — `run_lint_command` calls
  `lint_option_error(args)` before any file work and returns exit 2 with
  human (`Error: ...`) or JSON (`lint-error`) output on any validation error.
- `src/app/io/cli_lint_commands.spl:217-218` — any unrecognized dash-prefixed
  arg returns `unknown option: {arg}` (covers `--bogus`, including the
  `--json --bogus` case since `--json` is an accepted flag at line 185).
- `src/app/io/cli_lint_commands.spl:210-211` — empty `--profile=` returns
  `--profile requires a tier`; bare `--profile` is caught at lines 233-234.
- The focused contract exists at
  `test/01_unit/app/lint_cli_option_validation_contract_check.spl` and
  asserts exit 2 for `--bogus`, bare `--profile`, empty `--profile=`, and
  `--json --bogus`, plus the help-mixing cases.

Execution limit: running the contract under the pinned Rust seed
(`bin/simple.exe run`, v1.0.0-rc.1) fails before the contract body with
`unknown decorator '@representation_boundary'` on a transitively imported
module — the known release/1.0.0 source/binary inconsistency from
cfd89933699. The remaining "pure-Simple qualification" step (running the
contract on a Stage 4 self-hosted CLI) is unchanged and still pending; the
source-level defect described in this doc is fixed.
