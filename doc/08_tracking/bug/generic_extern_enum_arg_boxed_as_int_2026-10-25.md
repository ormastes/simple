# Struct/enum handles boxed as integers by rt_value_int_wide (2026-10-25)

## Class
Stage-2-compiled code passes a struct, class or enum HANDLE through
`rt_value_int_wide` (the integer box: `v << 3`) whenever the value's static
type is lost or erased to i64 at a generic/container boundary. The handle comes
out as `handle << 3` (e.g. `0x5555572449088` for `0xaaaaae489211`); any reader
that treats the slot as the struct then dereferences a wild pointer, and
runtime probes (promotion, discriminant) see a scalar.

## Sites hit by Phase 3 Stage 3 hello world (all binary-patched by NOPing the one `blr rt_value_int_wide`, x0 already holds the raw handle)
| # | site | source shape | effect |
|---|------|--------------|--------|
| B4 | driver_source_pipeline_parsing: parse_full_frontend_selected_v1 (+2 in add_streaming_module_surface), driver_hir_pipeline_lowering: lower_streaming_surface_source | `rt_transient_heap_promote<T>(parsed)` with a Result/selected local | promotion is a scalar no-op; Result freed at scope end; `.unwrap()` on a freed Result panics |
| B6a | hir_lowering module_build lower_module (module_build.spl:571 on the Phase 3 base) | untyped `val fn_key = if real_id.is_valid(): real_id else: SymbolId(id: lower_idx)` then `functions[fn_key] = hir_fn` | Dict<SymbolId,_> key stored boxed; hc_enc_hir_module SEGV on keys()[0]. Source workaround landed on release/1.0.0 (#4634): `val fn_key: SymbolId = ...` (module_build.spl:576); see `untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25.md` |
| B7-inv | driver_pipeline_lowering lower_to_mir_with_target_context (enum inventory) | `if val present = opt: arr.push(present)` | register_module_enum_inventory_v1 SEGV |
| B8 | mir_array_move am_children (36 pushes) | `exprs.push(x)` / `blocks.push(b)` of struct payloads bound by `case` | am_expr_has_place_let SEGV |
| B9 | switch_operators_calls `_sffi_enum_discriminant$i64` (an inferred `i64` instantiation; no explicit `<i64>` exists in source) | `_sffi_enum_discriminant(HirExprKind.Call(...))` | every disc probe returns -1; "unsupported MIR expression" for Call |

Objects: S/r27/bp/objs/{driver_source_pipeline_parsing_p3b4,driver_hir_pipeline_lowering_p3b4,module_build_p3b6,driver_pipeline_lowering_p3b7,mir_array_move_p3b8,switch_operators_calls_p3b9}.o.
Scripts: S/r27/bp/patch_intbox.py (NOP every int_wide feeding a named sink inside named functions), S/r27/bp/patch_at.py (NOP one asserted `blr` at fn+offset).
Finding sites: gdb conditional breakpoints on rt_array_push / rt_dict_set / rt_transient_heap_promote with
`($x1 & 7) == 0 && (($x1 >> 3) & 7) == 1` (an int-boxed heap handle).
A static census cannot separate these from genuine integer boxing (2,700+
int_wide -> push/set sites), so the safe NOP is applied only where every
pushed value is a struct/enum handle.

## Why NOP is safe
`rt_value_as_int_wide` already passes a heap-tagged value through unchanged,
so a raw handle round-trips through any int-unboxing reader; the patched sites
store struct/enum values only.

## Compiler fix (open)
MIR must not erase a struct/enum/Result local to i64 at: if-expression results
of struct type, `if val x = opt` payload bindings, `case` payload bindings
pushed into typed arrays, and inferred `i64` instantiations of generic
externs called with enum arguments (generic inference picks `i64` for
`_sffi_enum_discriminant(EnumCtor)`; it must instantiate with the enum type). Takes effect once Phase 3
rebuilds itself.

## Related records
- `untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25.md` -- B6a, with the landed source workaround.
- `optional_struct_stored_into_desugared_field_keeps_option_box_2026-10-25.md` -- the "Stage 3 B7" there is a
  different site and root cause (`T?` Option box stored into a desugared `has_x/x` field in
  declaration_lowering / class_declaration_lowering). This record's enum-inventory push is labelled B7-inv to
  keep the two apart.
