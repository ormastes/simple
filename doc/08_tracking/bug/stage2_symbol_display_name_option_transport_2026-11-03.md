# Frozen stage2: `symbol_display_name` transports `HirSymbol?` through `if val`, so every NamedVar carries a garbage name and MIR reports "undefined variable (false, )"

- **ID:** stage2_symbol_display_name_option_transport_2026-11-03
- **Priority:** P1 (phase 3: no stage3-compiled program with a local variable lowers; `val s = "x"; print(s)` still fails MIR after the local-index mirror of stage2_local_symbol_index_bucket_tagged_id_2026-11-03)
- **Status:** fix-implemented-verification-pending (2026-11-08). Source workaround in `src/compiler/20.hir/hir_symbol_table_methods.spl` (`symbol_display_name` reads the name through the scalar accessor `symbol_name_scalar_raw`, which already exists for exactly this hazard), plus the 2026-11-08 hot-site sweep below. The stage2 miscompile itself is not fixed; native stage3 verification is pending.

## Symptom
Stage3 candidates built from the hirfix2c objects (`s3_fable12.exe`, `s3_fable12c.exe`, F3 lane `s3_fable13.exe`; objects by the
frozen stage2 ef0681fc0e1) compiling `fn main(): val s = "x"; print(s)` report
`MIR lowering error: undefined variable (false, ) at ...fable_variable.spl:3:10`. The NAME in the diagnostic is the text
`(false, )` — the rendering of a failed `(bool, text)` lookup — for every variable, in every lineage since S3N-4. hello
(no locals) compiles and runs.

## Root cause
`expr_dispatch.spl` builds the diagnostic from the NamedVar payload (`_sffi_tuple_get<text>(named_var_payload, 1)`), and the
payload is produced during HIR lowering at `expression_core.spl:919`:
`HirExprKind.NamedVar(found_symbol, self.symbols.symbol_display_name(found_symbol, ident_name_t))`.
`symbol_display_name` (`hir_symbol_table_methods.spl:326`) is five lines in which the frozen stage2 miscompiles two shapes at once:

```
if id.?:
    val raw: i64 = id.id
    val found: HirSymbol? = self.symbols[raw]
    if val payload = found:          # class (b): `if val x = <struct Option>` bound through rt_value_as_int_wide
        val sym: HirSymbol = payload
        return sym.name              # reads a field of the mis-bound payload
fallback
```

So the NamedVar's text is garbage, and (same function, same transport) the symbol the MIR Var/NamedVar arms look up is not the
one `bind_local` registered: faulting-prologue dumps on the fresh `mir_lowering_types` object (veh_15700, veh_87916) show
`bind_local(symbol_id=1)` for `s` and the first `find_local(2)` for `print`, both raw/untagged — the local index and its Dict
mirror are consistent, the id arriving from the corrupt payload is not. Same class as
`get_symbol_raw`'s docstring and `symbol_name_scalar_raw`'s own rationale ("stage-native code can miscompile a struct-valued
Option returned across a function boundary").

## Workaround (this record)
`symbol_display_name` no longer binds the `HirSymbol?`: it returns `symbol_name_scalar_raw(id.id)` when non-empty, else
`fallback`. Behaviour change: a symbol whose stored name is empty now yields `fallback` instead of `""` (no caller relies on an
empty display name; every caller passes the identifier as `fallback`). Pinned by
`test/01_unit/compiler/hir/symbol_display_name_scalar_shape_spec.spl`.

## Verification
- Base: `symbol_display_name` returns `sym.name` of an `if val`-bound payload (spec FAILS 0/2). The sibling mutators
  `mark_generic_callable` / `rename_symbol` keep the same `if val payload = found` shape; they write a symbol back rather
  than feeding a NamedVar name and are out of this record's scope.
- Fix: body routes through `symbol_name_scalar_raw`; spec PASSES (seed interpreter).
- Stage3 proof needs a stage2 closure rebuild of `compiler.hir.hir_symbol_table_methods` (next `fable_probe_hirfix` run after
  hirfix2d) and the variable smoke (`test/04_smoke/fable_variable.spl`, expect `x`).

## Re-scope (2026-11-07)
This cannot be fixed in source while stage2 is frozen. The miscompile, `if val payload = <HirSymbol?>`
bound through the scalar decode, is in the frozen stage2 binary's codegen. Every next-leaf object of
`hir_symbol_table_methods` is compiled by that same binary. The `symbol_name_scalar_raw` route is also the
correct shape under a correct compiler: it is behaviour-equivalent apart from the empty-name note above,
and `symbol_display_name_scalar_shape_spec` pins it. So the "workaround" carries no extra cost and is safe to
keep for good.

No free MIR probe slot was available (`.mir_slot.3` locked), so a stage2 rebuilt from current source could
not be checked. **Removal condition:** a stage2 rebuilt from current release/1.0.0, and a stage3 built from the
original `if val` body that passes `test/04_smoke/fable_variable.spl`. Until both exist, keep the workaround.

## Fix (2026-11-08, lane-f-optxport) — hot-site sweep of the same Option-transport shapes

Native evidence on 2026-11-08 (vb_mm1, `method_calls_literals.spl`, PRs #7814/#7831) widened the family beyond
`if val`: the frozen stage2 also mis-tests `text? != nil` and drops a `SymbolId?` built from a valid raw id
(`Some(SymbolId(id: raw))` then `!= nil`). This sweep audited `src/compiler/20.hir` and `src/compiler/50.mir`
for those shapes on the paths the native stage3 needs (identifier, call, let, NamedVar, static method call)
and rewrote 13 sites to the proven shapes: a raw `i64` id with `-1` = absent (`lookup_or_invalid(..).id`,
`SymbolId(id: raw)` only at the consumer), or an unwrapped `text` with `""` = absent (`?? ""` and the existing
`*_scalar_raw` accessors). Each site is tagged `# @workaround bug=stage2_symbol_display_name_option_transport_2026-11-03`.

| # | file | site | old shape -> new shape |
|---|------|------|------------------------|
| 1 | `20.hir/hir_lowering/_Expressions/expression_core.spl` | `ExprKind.Ident` lowering (every identifier) | `lookup(..)` + `symbol == nil or symbol.? == nil` -> `lookup_or_invalid(..).id >= 0` |
| 2 | same | `declared_static_method_resolution` owner kind | `HirSymbol? == nil` + `.kind` -> `symbol_is_type_declaration_scalar_raw(owner.id)` (new accessor) |
| 3 | same | `declared_static_method_resolution` method id | `if val declared_method = <SymbolId?>` -> `match ... case Some` into raw `i64`, `SymbolId(id: raw)` at the return |
| 4 | `20.hir/hir_lowering/_Expressions/call_arity.spl` | arity-row build per declared function | `symbol != nil and symbol.? != nil` -> `lookup_or_invalid(..).id >= 0` |
| 5 | `20.hir/hir_symbol_table_methods.spl` | new `symbol_is_type_declaration_scalar_raw` | sibling of `symbol_is_enum_declaration_scalar_raw` (Class/Struct/Enum) |
| 6 | `50.mir/_MirLoweringExpr/expr_dispatch.spl` | NamedVar by-name fallback | `lookup(..)` + `pre_resolved != nil` -> `lookup_or_invalid(..).id >= 0` |
| 7 | same | NamedVar foreign-owner retry | `if val foreign_symbol = get_symbol_raw(..)` + `if val foreign_owner = .defining_module` -> `symbol_defining_module_scalar_raw(..) != ""` |
| 8 | `50.mir/mir_lowering_stmts.spl` | `HirStmtKind.Let` binding symbol | `SymbolId?` rebuilt from a valid id + `.?` + `?? SymbolId(id: -1)` -> `let_symbol_raw: i64 >= 0` |
| 9 | `50.mir/_MirLoweringExpr/method_calls_literals.spl:2705` | static owner name recovery | `if val static_owner = get_symbol_raw(..)` -> `mir_class_identity_raw(..) != ""` (already `""` for a missing symbol) |
| 10 | same, static-method block | `static_receiver_symbol: SymbolId?` built from a valid id | dropped; `SymbolId(id: resolved_static_receiver_symbol)` under the existing `>= 0` test |
| 11 | same | `var static_method_id: SymbolId? = nil` (`== nil` x2, `!= nil`, `?? SymbolId(id: -1)`) | `var static_method_raw: i64 = -1`, `>= 0` / `< 0` tests, `SymbolId(id: raw)` at the dispatch |
| 12 | same | `unique_static_method != nil` | `match lookup_unique_static_method(..): case Some` into raw `i64` |
| 13 | same | `static_result_name: text?` from a class-field `Dict.get` tested `!= nil` | `val static_result_name: text = .. ?? ""`, test `!= ""` (the vb_mm1 shape) |

Behaviour notes: `lookup_or_invalid` additionally rejects a stale out-of-range binding (`found >= next_symbol_id`) that
`lookup` passed through as a `SymbolId`; a stale binding now lowers as unresolved instead of a NamedVar with a dead id.
Sites 9 and 7 are exact equivalents (both scalar accessors yield `""` for a missing symbol). The unresolved-owner
recovery region of `method_calls_literals.spl` (`unresolved-owner-get` .. `unresolved-owner-done`, vb_mm1 lane) was
not touched; `unresolved_owner_method_raw_id_guard_spec` still passes 4/4.

Out of scope (audited, left as is, candidates for a follow-up if native evidence names them): `expr_dispatch.spl`
function-value lowering (`optional_sym == nil` + `if val present_sym`, needs `name`/`type_`/`kind` together),
`module_declarations_bootstrap.spl` `owner_context: SymbolId?` (a parameter of `declared_callable_type`, not a test),
`SymbolTable.get_symbol(id: SymbolId?)` (parameter shape; hot callers already use `get_symbol_raw`), the 59
generated sites in `20.hir/generated/hir_codec.spl`, and the `match <SymbolId?>: case Option.Some` arms the vb_mm1
fixes left in place.

Specs:
- NEW guard `test/01_unit/compiler/50.mir/stage2_option_transport_hot_sites_guard_spec.spl` (12 examples, one per
  rewritten site family; 0/12 on the base shapes, 12/12 after).
- `test/01_unit/compiler/50.mir/if_val_binder_payload_spec.spl` 3/3, `unresolved_owner_method_raw_id_guard_spec.spl`
  4/4, `test/01_unit/compiler/hir/symbol_display_name_scalar_shape_spec.spl` 2/2 (seed interpreter).
- `test/01_unit/compiler/hir/declared_static_method_resolution_spec.spl` is 2/4 BEFORE and AFTER (the two positive
  owner cases fail on the unmodified base too; pre-existing, not introduced here, not root-caused in this lane).

Unverified: native. The seed interpreter cannot show the miscompile; proof is a stage2-closure rebuild of the six
touched objects and the stage3 variable / static-method smokes (`test/04_smoke/fable_variable.spl`,
`test/fixtures/compiler/native_unresolved_owner_method/`).
