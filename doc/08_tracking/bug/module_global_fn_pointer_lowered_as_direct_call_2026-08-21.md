# Module-global function-pointer slot lowers to a DIRECT call

Status: OPEN (pre-existing; not a regression from the 2026-08-21 50.mir work)
Spec: `test/01_unit/compiler/mir/module_global_function_pointer_lowering_spec.spl`
Verbatim: `Results: 1 total, 0 passed, 1 failed`

## Symptom
For

```
var cleanup: fn() = default_cleanup
fn install(): cleanup = replacement_cleanup
fn invoke(): cleanup()
```

MIR for `invoke` contains a `MirInstKind.Call` whose callee operand is
`MirConstValue.Str("cleanup")` — a DIRECT call bound at lowering time — so a
later reassignment through `install` is not observed. `StoreGlobal`,
`LoadGlobal` and `CallIndirect` are all also present; the defect is the extra
direct call, which the spec's last assertion pins
(`expect(saw_direct_cleanup_call).to_equal(false)`).

## Root cause (located)
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:4416`

```
if is_direct and self.local_map.has(mir_expr_symbol_id_value(direct_symbol)):
    is_direct = false
```

`is_direct` is demoted for LOCAL variables only. A module-global `var` holding
a function pointer is not in `local_map`, so a `Var`/`NamedVar` callee naming
it stays `is_direct` and reaches `emit_resolved_direct_call` (same file, ~:4699).

## Why no fix landed here
Two candidate predicates for demoting `is_direct` were tried and both are
blocked on missing information at that point:
- declared-type test (`HirTypeKind.Function`): the global's `HirSymbol.type_`
  is nil at MIR lowering, and `HirConst.type_.kind` matched none of 16 probed
  variants under the seed interpreter — the type is not available/decodable here.
- mutability test (`const_.is_mutable`, recorded into a `mutable_global_ids`
  side table): this DID remove the direct call, but then one of the
  `StoreGlobal`/`LoadGlobal`/`CallIndirect` observations went false, i.e. it
  moved the callee off the global-read path entirely. Reverted rather than
  shipped unverified.

Also note `find_global_static(sym)` returns nil for this global even though
`global_symbol_ids.contains(sym)` is true — a separate inconsistency worth
resolving first, since the LoadGlobal path keys off `find_global_static`.

## Fix note landed with this record
The spec's own import was wrong and masked the real failure: it did
`use compiler.mir.mir.*`, which does not re-export `MirLowering`
(`src/compiler/50.mir/__init__.spl` says to use `compiler.mir.mir_lowering`),
so the example errored with `semantic: variable MirLowering not found` before
reaching any assertion. That import is fixed; the spec now runs and fails on
the real defect above.
