# Native-build regression repros (2026-07-19)

Standalone `fn main() -> i64` programs that guard the 8-commit native-build fix
batch landed at origin `250bcb707f1`, plus later focused regressions. Each file
records its current evidence below; pending fixtures are not called gate-proven.
These are NOT
`_spec.spl` files, so the SSpec runner ignores them; a native harness consumes
them as `native-build --entry <file>` then checks the process exit code.

Run one:
```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 <self-hosted-simple> native-build --entry <file> -o /tmp/b && /tmp/b; echo rc=$?
```

| file | guards fix | commit | expected rc | status | regression looks like |
|------|-----------|--------|-------------|--------|-----------------------|
| `key3_struct_spread_paren.spl` | KEY3 native struct-spread (paren form) | f907796e57e | **103** | PASS | spread base dropped → wrong number |
| `w2_array_index_rw.spl` | W2 `local_mir_type_of` Option in `lower_array_lit` | e7c445145a7 | **72** | PASS | build-fail `unknown static method ptr on class MirType` |
| `c5_char_from_code.spl` | C5 integer builtin/owner precedence + Unicode runtime backing | source update | **42** | SOURCE FIX / execution pending | UFCS/custom dispatch, missing symbol, or ASCII-only result |
| `c9_string_parse_f64_to_upper.spl` | C9 `.parse_f64()`/`.to_upper()` MIR dispatch | 84701d8fb5e | **42** | PASS | unresolved-in-MIR / wrong value |
| `dict_struct_value.spl` | dict struct-value round-trip | (batch) | **73** | PASS | wrong value |
| `dict_fn_value.spl` | dict fn-value round-trip | (batch) | **33** | PASS | wrong value |
| `class_array.spl` | class + array interaction | (batch) | **42** | PASS | wrong value |
| `match_value.spl` | match value binding | (batch) | **7** | PASS | wrong value |
| `option_try_unwrap_ifval_XFAIL.spl` | `.?` + `if val` payload unwrap | — | **7** | **XFAIL** (gets 84) | origin Option-ABI regression |
| `enum_f64_payload_precision.spl` | LLVM enum f64 payload-word ABI | — | **30** | SOURCE FIX / execution pending | f64 bits numerically converted |

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

## SOURCE FIX: `enum_f64_payload_precision.spl`

Expected return is **30** on LLVM native-build. The backend bitcasts f64 payloads
into `rt_enum_new`'s i64 payload word; MIR bitcasts back only when the semantic
payload type is f64. The interpreter / Cranelift control remains in
`test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl`.
Current-source incremental execution is pending after the bounded mini build
reached its time cap.
