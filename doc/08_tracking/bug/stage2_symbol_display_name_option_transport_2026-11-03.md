# Frozen stage2: `symbol_display_name` transports `HirSymbol?` through `if val`, so every NamedVar carries a garbage name and MIR reports "undefined variable (false, )"

- **ID:** stage2_symbol_display_name_option_transport_2026-11-03
- **Priority:** P1 (phase 3: no stage3-compiled program with a local variable lowers; `val s = "x"; print(s)` still fails MIR after the local-index mirror of stage2_local_symbol_index_bucket_tagged_id_2026-11-03)
- **Status:** open. Source workaround in `src/compiler/20.hir/hir_symbol_table_methods.spl` (`symbol_display_name` reads the name through the scalar accessor `symbol_name_scalar_raw`, which already exists for exactly this hazard). The stage2 miscompile itself is not fixed.

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
