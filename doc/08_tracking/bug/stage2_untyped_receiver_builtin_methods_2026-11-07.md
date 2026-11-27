# Stage 2 MIR: builtin receiver methods rejected for lost or missing receiver types

- **Date:** 2026-11-07
- **Severity:** P1 (Stage 2 `compiler_cli_build`, bootstrap run 13)
- **Status:** fix-implemented
- **Related:** `stage2_optional_class_receiver_method_unresolved_2026-11-07.md` (PR #7367)

## Root causes and fixes

1. **Text parse aliases missing in the native text builtin table** (compiler). The
   interpreter treats `parse_int`, `parse_i32` and `parse_i64` as one strict
   `Option<i64>` arm, and `parse_float`, `parse_f64` and `parse_f64_safe` as one
   `Option<f64>` arm (`interpreter_method/string.rs:411,417`). MIR only knew
   `parse_int` and `parse_f64`.
   - Fix: `mir_text_parse_int_alias_v1` and `mir_text_parse_float_alias_v1` in
     `_MirLoweringExpr/method_calls_literals.spl` route the aliases to the same
     runtime (`rt_string_parse_int` and `rt_string_to_float`).
   - Clears 7 errors: dom_color ×2, dom_identity_index ×2, the HTML layout
     renderer, timing, and duplicate_check config.
2. **f64 `sqrt` had no native builtin** (compiler).
   - Fix: `try_lower_numeric_builtin` admits `sqrt` for float receivers only and
     lowers it to `rt_math_sqrt`. `int.sqrt()` is still rejected.
   - Clears skia geometry ×2.
3. **A numeric `var` loses its type when reassigned** (compiler). In
   `total = total + x`, the binop result carries no HIR type. The assignment then
   *forgot* the binding's `f64`, and `total.round()` had no receiver proof.
   - Fix: `builtin_keeps_numeric_type_on_assign` (called from
     `mir_lowering_stmts.spl`) keeps an int or float binding type when the
     assigned value's MIR class agrees with it.
   - Clears skia gpos `round`.
4. **Source that is genuinely untyped or misused:**
   - `hir_target_constraints.spl:83`: `index_of` returns `i64` (`-1` when not
     found) and never `nil`, so `eq == nil or eq.unwrap()` was wrong. Clears ×2.
   - duplicate_check: three empty `{}` literals of nested dict type are now
     annotated (`file_hashes`, `file_line_index_cache`, `line_index`). Clears
     interner `keys` and similarity `has`/`min`.

Spec: `test/01_unit/compiler/50.mir/text_parse_alias_float_sqrt_receiver_spec.spl`.
It passed 2 of 6 before the fix and 6 of 6 after.

## Not in this fix (with owner)

- **`DynSmfLoadedLibrary`** is declared both as a class (`os/smf/dynsmf_session.spl:22`)
  and as a struct (`os/smf/smf_dynlib.spl:212`). The resulting `has`/`remove`
  errors in dynsmf_owned_v2 (×4) and smf_dynlib (×1) belong to the
  owner-ambiguity lane.
- **Generic `T: Hash` receivers:** `arr.hash()` and `t.hash()` in `src/hash.spl`
  (×3), `key.hash()` in `src/map.spl`, and `entry.key == key` in
  `adaptive_map.spl`. These need trait-bound dispatch for builtin
  array and tuple `Hash`, which belongs to the generic-receiver lane.
- **`sha1`:** the API is typed with the untyped `list`. `v.to_array()` on a
  declared `Vec4i` is also unresolved: there are four tiered copies of
  `simd.spl`, so the owner is ambiguous.
- **`sdn_codec` `issue.line.to_text()`:** the element type is lost through the
  tuple payload `parsed.2`, which belongs to the payload-shape lane.
