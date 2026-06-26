# System Test Plan: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## First Slice

Use unit specs for helper behavior and the existing integration CLI spec for
log-mode behavior.

Add or extend:

- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`

Keep:

- `test/02_integration/app/context_log_modes_spec.spl`

## Acceptance Checks

- `simple check src/app/io/cli_ops.spl test/01_unit/app/tooling/context_generate_spec.spl test/unit/app/tooling/context_generate_spec.spl`
- `simple test test/01_unit/app/tooling/context_generate_spec.spl --mode=interpreter --clean`
- `simple test test/unit/app/tooling/context_generate_spec.spl --mode=interpreter --clean`
- `simple test test/02_integration/app/context_log_modes_spec.spl --mode=interpreter --clean`
- `sh scripts/audit/direct-env-runtime-guard.shs --working`
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`

