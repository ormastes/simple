# Language Policy System Specs - Feature Expert

System specs under `test/03_system/language/policy/`, manuals under
`doc/06_spec/03_system/language/policy/`. Files tagged `@tag:in-development` in
the header are expected to fail and are skipped in whole-suite runs.

## Group: diag

- `nil_unsafe_only_spec.spl` (+ `nil_unsafe_only_staged_spec.spl`) - nil only in unsafe; case None on scalar
- `match_exhaustive_spec.spl` (+ `match_exhaustive_staged_spec.spl`) - MEXH001 warning, critical error, staged error
- `any_unsafe_only_spec.spl` - W/E-ANY-COMPILE-001 outside unsafe(type_erasure)
- `option_if_while_bind_spec.spl` (+ `option_if_while_bind_staged_spec.spl`) - if val / while val bind payload
