# Module-global function-pointer slot lowers to a DIRECT call

Status: RESOLVED 2026-08-21 (see the RESOLVED section at the end)
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

## RESOLVED 2026-08-21 (pure-Simple, 50.mir)

Fixed in three places, all in `src/compiler/50.mir` (no seed change, no
redeploy needed — the spec runs the pure-Simple lowering as a library):

1. `_MirLoweringExpr/expr_dispatch.spl` — the `NamedVar` read path had NO
   case for a top-level function named as a VALUE: `default_cleanup` on the
   right of `var cleanup: fn() = default_cleanup` (and of
   `cleanup = replacement_cleanup`) fell through to
   `error("undefined variable ...")`, so the whole binding was dropped. Now
   emits the same `Const(Str(name), FuncPtr(..))` shape
   `named_function_operand` already produces for a function passed as a call
   argument, gated on `is_known_top_level_function`.
2. `_MirLowering/module_lowering.spl` — new `hir_const_is_function_slot` +
   its use in `lower_runtime_module_initializers_named`. The declared type
   arrives as `HirTypeKind.Any` (probed: the `fn()` annotation does not
   survive HIR lowering — this is why the record's declared-type candidate
   predicate failed), so the free, type-driven
   `runtime_module_initializer_supported` rejects the binding and it got no
   static at all. Function slots are now appended to the runtime-initializer
   list, which creates the `MirStatic` and emits the init-time `StoreGlobal`.
   With a backing static present, the pre-existing write hook
   (`mir_lowering_stmts.spl:1218`) emits `StoreGlobal` for `install` and the
   read hook (`try_lower_global_read`) emits `LoadGlobal` for `invoke`.
3. `_MirLoweringExpr/switch_operators_calls.spl:4418` — the `is_direct`
   demotion now also fires for a callee that names a module global WITH
   backing static storage and is NOT a known top-level function. This is the
   predicate the record was looking for: neither declared type (unavailable)
   nor mutability (too coarse — it moved the callee off the global-read path),
   but "is a global slot, not a function name". `find_global_static(sym)` no
   longer returns nil for this global, because (2) gives it a static.

### Evidence

```
bin/simple test test/01_unit/compiler/mir/module_global_function_pointer_lowering_spec.spl
Results: 3 total, 3 passed, 0 failed     (was: 1 total, 0 passed, 1 failed)
```

Two neighbour examples were added to the same spec and are part of that
3/3: an over-demotion guard (an ordinary `helper()` call must stay a DIRECT
call) and the initializer half (the slot must get a `MirStatic` plus an
init-time `StoreGlobal`). Mirrored to
`test/unit/compiler/mir/module_global_function_pointer_lowering_spec.spl`.

Neighbours: all 81 specs under `test/01_unit/compiler/mir/` were run
individually before and after the change (the "before" run used byte-exact
pre-edit copies of the three files, not `HEAD`, since the tree carries other
sessions' uncommitted edits). 26 of them fail, with **identical**
`Results:` lines on both sides — zero regressions, one spec fixed.

### Known follow-up (backend, NOT fixed here — different owner)

At MIR level a function reference is `Const(Str(name), FuncPtr(..))`, which
is the established shape (`named_function_operand`, `lower_lambda_value`).
`_MirToLlvm/core_codegen.spl:translate_const_value` renders `Str(v)` as a
`getelementptr` to a string literal regardless of the operand's MIR type, so
a FuncPtr-typed `Const(Str)` reaching a native build would materialise the
NAME, not the function address. That path is only reachable now that
function-slot globals exist; it needs a FuncPtr-typed `Str` case emitting
`@name` in the LLVM backend (`src/compiler/70.backend`, owned by the
bootstrap lane this session was fenced out of). Filed here rather than
silently normalised.
