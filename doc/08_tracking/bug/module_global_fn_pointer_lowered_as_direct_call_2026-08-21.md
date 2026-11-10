# Module-global function-pointer slot lowers to a DIRECT call

Status: FIXED (2026-11-11, lane ne15) — the demote-when-global-slot fix named
after this bug is present at `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(~:8937-8948); the pinning spec no longer reaches the assertion for unrelated
spec/seed drift. See addendum.
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


## Addendum 2026-11-11 (lane ne15) — FIXED; global-slot demote landed, pinning spec drifted

**Code evidence at tip f7640d20a458**
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:8937-8948`):
a comment block naming this bug documents the landed fix — a callee naming a
module global with backing static storage that is not a known top-level
function is demoted from `is_direct`:

```simple
if is_direct and not self.is_known_top_level_function(direct_name, direct_symbol):
    val slot_symbol_id = mir_expr_symbol_id_value(direct_symbol)
    if slot_symbol_id >= 0 and self.global_symbol_ids.contains(slot_symbol_id):
        if self.find_global_static(slot_symbol_id).?:
            is_direct = false
```

so `var cleanup: fn() = default_cleanup` reassigned via `install()` is
observed by `cleanup()` through the LoadGlobal/CallIndirect path. The
adjacent local/param demotion (same site, ~:8926-8931) covers fn-typed
parameters. This is exactly the predicate this doc said was missing; the
`find_global_static`-returns-nil inconsistency noted here is also surfaced by
the `?.` guard in the new code.

**Spec status (seed-smoke, same tip):** the pinning spec
`test/01_unit/compiler/mir/module_global_function_pointer_lowering_spec.spl`
now fails 0/4 BEFORE reaching any assertion, for unrelated drift:

- example 1 references `bootstrap_mir_static_remap_add`, which no longer
  exists anywhere in `src/compiler` (the remap API was removed/renamed);
- examples 2-4 stop at a seed visibility error — `private fn
  compiler_value_discriminant of module 00.common/value_access.spl is not
  visible to 50.mir/_MirLoweringExpr/expr_dispatch.spl` — while current
  `expr_dispatch.spl:55` named-imports it and the self-hosted compiler
  accepts that import, i.e. a seed/self-hosted visibility divergence on the
  compiler module graph, not this defect.

Observed: `Results: 4 total, 0 passed, 4 failed`.

**Follow-up (not this row):** the spec needs a refresh against current
compiler internals, and the seed visibility divergence on
`compiler_value_discriminant` deserves its own row, before the spec can serve
as a runtime fence again. The code-level fix this doc asked for is present at
HEAD; no seed-side equivalent was inspected beyond noting the spec cannot
compile the compiler graph under the seed's stricter visibility pass.
