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
| `option_try_unwrap_ifval.spl` | `.?` + `if val` payload unwrap (i64) | see below | **7** | **PASS** | Some-tag leaks into payload |
| `option_try_unwrap_ifval_text.spl` | `.?` + `if val` payload unwrap (text) | see below | **42** | **PASS** | payload leaks/misdecodes |
| `option_try_unwrap_ifval_struct.spl` | `.?` + `if val` payload unwrap (struct) | see below | **42** | **PASS** | fields misread (both default to index 0) |
| `option_try_unwrap_ifval_none.spl` | `.?` + `if val` None short-circuit (i64) | see below | **42** | **PASS** | None wrongly treated as Some |
| `option_try_unwrap_ifval_float.spl` | `.?` + `if val` payload unwrap (f64/f32) | source update | **42** | SOURCE FIX / execution pending | raw payload bits reached a numeric cast instead of a bitcast |
| `option_nullcoalesce_struct.spl` | `??` payload struct field-name provenance (Some side) | see below | **42** | **PASS** | fields misread (both default to index 0) |
| `option_nullcoalesce_struct_none.spl` | `??` default-expr struct field-name provenance (None side) | see below | **42** | **PASS** | fields misread (both default to index 0) |
| `enum_f64_payload_precision.spl` | LLVM enum f64 payload-word ABI | — | **30** | SOURCE FIX / execution pending | f64 bits numerically converted |
| `struct_array_push_i64_field_tagshift.spl` | struct pushed into an empty-literal `[]`-declared array (i64 fields) | (this fix) | **30** | PASS | SIGSEGV, or a specific 11x rc marking which field/element mismatched |

## RESOLVED: `option_try_unwrap_ifval*.spl` (i64/text/struct/none)

Was an **origin-base regression** (origin `d71449a "restore canonical Option
ABI"`) tracked in
`doc/08_tracking/bug/hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`.
Root-fixed 2026-07-20 with two independent defects:

1. **f64/f32 payload encode** (`ensure_option_handle`,
   `switch_operators_calls.spl`): a float-typed payload passed straight into
   `rt_enum_new`'s i64-declared parameter let the generic call-argument
   coercion pick `fptosi` (numeric truncation) instead of a bit-preserving
   transfer — the matching decode (`enum_payload_value`'s F64 arm) does a
   plain `bitcast`, so encode/decode disagreed on representation. Fixed by
   bitcasting float payloads to i64 explicitly before the call, mirroring
   `box_runtime_value`'s existing F64/F32 arms (`expr_dispatch.spl`). Verified
   correct via `SIMPLE_KEEP_LLVM_IR=1`: the payload now round-trips through a
   real `bitcast double %l1 to i64`, not `fptosi`.
2. **struct field-name provenance** (`ExistsCheck` lowering,
   `expr_dispatch.spl`): the merged result local had no
   `struct_value_syms`/HIR-type registration, so `resolve_field_index`
   silently defaulted every field name to index 0 (`p.x` and `p.y` both read
   field 0). Fixed by registering the Option's inner struct name onto
   `result_local`, preferring `option_inner_hir_type_for_local` (canonical
   tagged handle) and falling back to `struct_value_syms.get(base_local.id)`
   directly for the "raw migration form" (a struct pointer assigned straight
   to a `T?` binding without ever going through `ensure_option_handle`, since
   the pointer's own non-nil-ness already distinguishes Some/None).

`option_try_unwrap_ifval_XFAIL.spl` renamed to `option_try_unwrap_ifval.spl`
(now PASS, rc=7). Same "Some payload not extracted" family as the recurring
class in `doc/08_tracking/bug/baremetal_option_field_unwrap_faults_class_2026-07-18.md`
(see `feedback_recurring_problem_team_analysis_and_tests`).

## RESOLVED: `option_nullcoalesce_struct*.spl` (`??` shares the ExistsCheck struct gap)

`NullCoalesce` (`x ?? default`, `expr_dispatch.spl`, the case arm immediately
above `ExistsCheck` in the same file) uses the EXACT SAME
`option_payload_or_self`/`decode_runtime_value`/`enum_payload_value` helper
chain as `ExistsCheck`, and was proven — by direct probe, not assumption — to
share the identical struct field-misread defect: `val v = x ?? P(x: 7, y: 8)`
on a struct `Option` returned **33** (`v.x`/`v.y` both read field 0) instead
of **42**, on BOTH the Some-branch (`x` present) and the None-branch (the
`default` expression's own fresh construction — confirmed by re-testing with
DISTINCT field values after an initial same-value probe gave a false
negative). Fixed the same way as `ExistsCheck`: register the merged struct
name onto `result_local`, trying (1) `option_inner_hir_type_for_local` on the
left/Option operand, (2) `struct_value_syms` on `left_local` (raw migration
form), (3) `struct_value_syms` on `right_local` (the default expression's own
construction) once it exists.

## SOURCE FIX: `option_try_unwrap_ifval_float.spl`

Previously returned **1**, expected **42** (i.e. `v == 3.5` was false). The f64/f32 **encode**
side is fixed (see above — verified bit-correct in the LLVM IR). The
**decode/consumption** side is a *separate*, deeper defect: `ExistsCheck`'s
merged result local is intentionally kept i64-typed (`alloca i64`, uniform
raw bits) because the outer `if val v = x.?:` desugars to a direct
`icmp ne i64 <merge>, 3` sentinel comparison — i64/text/struct/bool all
survive that uniform slot because `ptrtoint`/`inttoptr`/`trunc`-low-bit are
bit-preserving, but f64 is the only payload type whose correct round-trip
through that slot needs a `bitcast`, not the generic `sitofp`/`fptosi` the
backend's argument/copy coercion otherwise picks. Attempting to make
`ExistsCheck`'s own result local F64-typed breaks the None-branch sentinel
emission (`emit_const(result_local, Int(3), F64)` is invalid LLVM IR: "add
double 3, 0") and desyncs from the outer sentinel comparison, which is not
type-aware. The consumer fix keeps that raw sentinel comparison unchanged,
then temporarily binds `v` to the existing typed payload decoder while
lowering the present branch. Existing `local_hir_types` provenance carries
the f64/f32 inner type; no parallel Option representation was added. Rebuilt
execution is pending.

## SOURCE FIX: `enum_f64_payload_precision.spl`

Expected return is **30** on LLVM native-build. The backend bitcasts f64 payloads
into `rt_enum_new`'s i64 payload word; MIR bitcasts back only when the semantic
payload type is f64. The interpreter / Cranelift control remains in
`test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl`.
Current-source incremental execution is pending after the bounded mini build
reached its time cap.
