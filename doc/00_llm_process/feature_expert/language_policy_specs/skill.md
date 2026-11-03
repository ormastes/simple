# Language Policy System Specs - Feature Expert

System specs under `test/03_system/language/policy/`, manuals under
`doc/06_spec/03_system/language/policy/`. Files tagged `@tag:in-development` in
the header are expected to fail and are skipped in whole-suite runs.
Engine-parity specs (char group) need `SIMPLE_BIN` set to the admitted `simple` executable.

## Group: diag

- `nil_unsafe_only_spec.spl` (+ `nil_unsafe_only_staged_spec.spl`) - nil only in unsafe; case None on scalar
- `match_exhaustive_spec.spl` (+ `match_exhaustive_staged_spec.spl`) - MEXH001 warning, critical error, staged error
- `any_unsafe_only_spec.spl` - W/E-ANY-COMPILE-001 outside unsafe(type_erasure)
- `option_if_while_bind_spec.spl` (+ `option_if_while_bind_staged_spec.spl`) - if val / while val bind payload

## Group: char (ADR-005)

- `char_index_spec.spl` (+ `char_index_in_dev_spec.spl`) - s[i] code-point indexing, interp/JIT parity
- `char_literal_spec.spl` (+ `char_literal_in_dev_spec.spl`) - char/raw/interpolated/triple-quoted literals
- `char_value_rules_spec.spl` (+ `char_value_rules_in_dev_spec.spl`) - never falsy, never int, surrogate rejection
- Probes: `probe/char_*.spl`
- test/03_system/language/policy/class_ref_interp_jit_consistency_spec.spl (+ _indev_spec.spl, probe/class_ref_probe.spl)
- test/03_system/language/policy/dict_get_option_spec.spl (+ _indev_spec.spl, probe/dict_get_option_probe.spl)
- test/03_system/language/policy/u64_field_store_spec.spl (+ _indev_spec.spl, probe/u64_field_probe.spl)
