# Native-build regression repros (2026-07-19)

Standalone `fn main() -> i64` programs that guard the 8-commit native-build fix
batch landed at origin `250bcb707f1`, plus the `.?` Option-unwrap origin
regression. Each is a **gate-proven** repro — the exact program the native-smoke
gate ran green (or, for the XFAIL, red at the documented value). These are NOT
`_spec.spl` files, so the SSpec runner ignores them; a native harness consumes
them as `native-build --entry <file>` then checks the process exit code.

Run one:
```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 <seed> native-build --entry <file> -o /tmp/b --clean && /tmp/b; echo rc=$?
```

| file | guards fix | commit | expected rc | status | regression looks like |
|------|-----------|--------|-------------|--------|-----------------------|
| `key3_struct_spread_paren.spl` | KEY3 native struct-spread (paren form) | f907796e57e | **103** | PASS | spread base dropped → wrong number |
| `w2_array_index_rw.spl` | W2 `local_mir_type_of` Option in `lower_array_lit` | e7c445145a7 | **72** | PASS | build-fail `unknown static method ptr on class MirType` |
| `c5_char_from_code.spl` | C5 `rt_char_from_code` runtime backing | fcd28794cd7 | **42** | PASS | build-fail / missing symbol |
| `c9_string_parse_f64_to_upper.spl` | C9 `.parse_f64()`/`.to_upper()` MIR dispatch | 84701d8fb5e | **42** | PASS | unresolved-in-MIR / wrong value |
| `dict_struct_value.spl` | dict struct-value round-trip | (batch) | **73** | PASS | wrong value |
| `dict_fn_value.spl` | dict fn-value round-trip | (batch) | **33** | PASS | wrong value |
| `class_array.spl` | class + array interaction | (batch) | **42** | PASS | wrong value |
| `match_value.spl` | match value binding | (batch) | **7** | PASS | wrong value |
| `option_try_unwrap_ifval_XFAIL.spl` | `.?` + `if val` payload unwrap | — | **7** | **XFAIL** (gets 84) | origin Option-ABI regression |

## XFAIL: `option_try_unwrap_ifval_XFAIL.spl`

Returns **84**, expected **7** — the Some-branch is taken but the payload leaks
unextracted. This is an **origin-base regression** (origin `d71449a "restore
canonical Option ABI"`), NOT a batch defect: the same batch produced 7 at the
pre-`d71449a` base and 84 after. Tracked in
`doc/08_tracking/bug/hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`.
Flip to expected-PASS (rc=7) once that bug is fixed. Same "Some payload not
extracted" family as the recurring class in
`doc/08_tracking/bug/baremetal_option_field_unwrap_faults_class_2026-07-18.md`
(see `feedback_recurring_problem_team_analysis_and_tests`).

## XFAIL: `enum_f64_payload_precision_XFAIL.spl`

Returns **40** on native-build, expected **30** — an f64 enum payload
(`0.1`) is lost. The 2026-07-19 MIR-lowering fix (the `rt_enum_payload`
F64 extract emits an `F64->F64` bit-reinterpret instead of the tagged-float
mask `(bits>>3)<<3`) makes this correct on the interpreter + cranelift; see
`test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl` (2/2).
native-build has a SEPARATE, deeper defect (construct passes the f64
payload in xmm0 instead of bitcast-to-i64; extract sitofp-coerces), tracked
in `doc/08_tracking/bug/native_llvm_f64_enum_payload_argpass_2026-07-19.md`.
Flip to expected-PASS (rc=30) once that backend fix lands. Same tagged-float
family as the recurring `<<3`/`>>3` tag-box class.
