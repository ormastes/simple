# Native `d[k]` on Dict<text, bool> yields int 1/0 (2026-10-25)

Found via PR #4504 (HIR codec `put_bool` wrote 1/0 / `N`).

## Root cause
`lower_dict_runtime_read` (src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl)
trusted the builder-tracked `Dict(K, V)` MIR type first. For field projections
and codec temps that type is the erased `Dict(_, i64)` default, so the HIR value
type (`bool`) was never consulted and `decode_runtime_value` took the integer
`>>3` arm: tagged true (11) -> 1, false (0) -> 0, typed i64.

## Fix
When the resolved V is I64 but the HIR V lowers to Bool, decode as Bool
(`raw == 11`), the same arm `.get()` uses since 7e83e92ce31.

## Regression
test/01_unit/compiler/50.mir/dict_bool_index_read_spec.spl — not yet run: only
the Rust seed is available on the Windows host and it fails to parse
`src/lib/nogc_sync_mut/io/windows_redirected_process.spl`. Needs a native
stage rerun to confirm.

## Related
- doc/08_tracking/bug/mir_unresolved_method_on_enum_payload_binding_2026-10-25.md
- doc/07_guide/language/dict_native_pitfalls.md
