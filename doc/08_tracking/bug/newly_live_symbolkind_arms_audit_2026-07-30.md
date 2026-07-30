# Audit: `case SymbolKind.X:` / bare-name arms that went from permanently-dead to live after PTR1/PTR2

- **Date:** 2026-07-30
- **Lane:** DEAD1 (mission-critical hardening campaign)
- **Scope:** every `match <symbol-expr>.kind:` arm across `src/compiler/**` whose case label is one
  of the 11 variants that collided with a `parser_types.spl` struct name before commits
  `5de6f3c56e8` (PTR1) and `3eb2635ea5c` (PTR2): `Function`, `Module`, `TypeParam`, `Class`,
  `Struct`, `Enum`, `Trait`, `Const`, `Import`, `Field`, `TypeAlias`.
- **Method:** repo-wide grep for `case SymbolKind\.` (qualified form) plus a second pass over every
  `match <var>.kind:` block whose `<var>` is a `Symbol`/`HirSymbol` value (traced by variable name
  and by reading the enclosing function signature/struct field), since most production call sites
  write **bare** case labels (`case Struct:`, `case Class | Struct | Enum:`) rather than
  `SymbolKind.Struct`. `ScopeKind` was checked the same way.

## Headline finding

`SymbolKind` is matched in exactly **2 places** with the fully-qualified `SymbolKind.X:` syntax
that a naive grep for `case SymbolKind\.` would find (`hir_types.spl:237-240`, `hir_types.spl:459`).
Every other production match arm on a `Symbol.kind` value uses **bare** case labels
(`case Struct:`, `case Class | Struct | Enum | Import:`), which are exactly as exposed to the
bare-name collision as the qualified form (per DISC2's finding that qualification does not
protect against the seed's flat name registry). A grep limited to `case SymbolKind\.` therefore
misses the majority of the newly-live surface. **`ScopeKind` has zero `case` arms anywhere in
`src/compiler/**`** — it is only ever constructed (`ScopeKind.Module`, `.Function`, `.Block`,
`.Class`, `.Loop`, `.Impl`), never matched, so it contributes 0 rows to this audit.

`90.tools/query_helpers.spl` / `query_api.spl` match `QuerySymbolKind` (already renamed away from
`SymbolKind` by DISC1's supplementary fix) with fully-qualified labels and do not import
`parser_types` — confirmed out of scope, not included below.

## Classification table

| File:line | Enum.variant (arm) | Class | One-line reason |
|---|---|---|---|
| `20.hir/hir_types.spl:237-240` | `SymbolKind.Class\|Struct\|Enum\|Trait` (`is_type_symbol` in `SymbolTable.define`) | REVIEW | Gates "first-write-wins" symbol dedup for type-level symbols; was permanently `false` (every `define()` call created a fresh `HirSymbol` row even when the name was already bound in-scope), now really dedups — changes `SymbolId` allocation/count for every Class/Struct/Enum/Trait definition compiler-wide. |
| `20.hir/hir_types.spl:459` | `SymbolKind.Function` (`lookup_function`) | REVIEW | Whole function always returned `nil` before; now returns the real `SymbolId` when the looked-up name is a function. |
| `20.hir/hir_types.spl:493-496` | bare `Function` (`lookup_method_in_type`, alongside working `Method`) | REVIEW | Adds a second, previously-dead match branch ("Static methods") to a function that already worked for `Method`-kind symbols; now also resolves `Type::method`-qualified `Function` symbols through this path. |
| `20.hir/hir_types.spl:542-544` | bare `Function` (`lookup_static_method`) | REVIEW (high) | This function's **entire documented purpose** ("Look up a static method... static methods are stored as Function symbols") was unreachable — it always returned `nil`. It is now functional for the first time. |
| `20.hir/hir_types.spl:624-629` | bare `Function` (`get_all_functions`) | SAFE | Pure list-building for did-you-mean error suggestions; was always `[]`, now returns real names. No crash risk, diagnostics-only. |
| `35.semantics/value_struct_layout.spl:20-23` | `SymbolKind.Struct` (`value_layout_symbol_is_struct`) | REVIEW (**highest**) | Sole gate for `validate_value_struct_layouts`, called from `80.driver/driver_hir_pipeline_lowering.spl:130,212,355` and hard-failing via `ctx.add_error(...)` (line 52 of that file). Was **100% dead** — the by-value-struct-cycle safety check has never rejected anything, ever, since it shipped. **Zero test coverage found repo-wide** (`grep -rl "validate_value_struct_layouts\|value_layout_symbol_is_struct" test` → no hits). |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl:365-369` | bare `Struct \| Enum` (`vhdl_catalog_type_identity`) | REVIEW | Now returns a real `"{owner}::{name}"` qualified identity string instead of always falling through to the caller's fallback name. |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl:378-382` | bare `Variable` | n/a (control) | `Variable` is **not** one of the 11 colliding names — unaffected, listed for contrast only. |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl:636-647` | bare `Struct \| Enum` | REVIEW | Populates the cross-module `rebase: Dict<i64,i64>` used to unify VHDL type-symbol identities across modules; was always skipped for type symbols before. See "Observed test regression" below — correlation only, not proven causation. |
| `35.semantics/resolve_strategies.spl:304-314` | bare `Class \| Struct \| Enum \| Import` (`is_static_method_call`) | REVIEW (**highest**) | The **sole** predicate deciding static-vs-instance dispatch for every `MethodCall` in `resolve.spl:348` (`resolve_expr`). Was permanently `false` — every `Type.method()` call in the entire compiler was resolved through the *instance* method path (`resolve_method`), never `resolve_static_method`. Now correctly routes static calls. This is the single highest blast-radius arm in this audit. |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:906-918` | bare `Class \| Struct \| Enum \| Import` (×2, sets `static_receiver_name`) | REVIEW (high) | Gate variable for the entire static-method MIR-lowering fallback chain further down the same function (see next 2 rows); was always `""`, so that whole fallback chain was unreachable dead code. |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:2293-2295` | bare `Function` | REVIEW | Inside the now-reachable fallback chain: confirms a `lookup_method_in_type` hit is Function-kind before emitting a direct static call (`emit_resolved_direct_call`) — real codegen side effect, previously unreachable. |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:2312-2318` | bare `Class \| Struct \| Enum` | REVIEW | Overrides the inferred `static_return_type` to a `MirTypeKind.Struct(...)` for the same fallback chain; previously unreachable. |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:448-453` | bare `Struct` (Result `.unwrap()`/`.unwrap_err()` payload) | REVIEW | Previously fell through to `error_fatal("unsupported Result {op} payload type")` for any `Result<StructType,_>` unwrap reaching this gap; now succeeds and sets `result_struct_name`. A compile-error→success flip for a real user-code shape. |
| `50.mir/_MirLoweringExpr/expr_dispatch.spl:2604-2611` | bare `Struct` (`??` / nil-coalesce merge, struct-name provenance) | REVIEW | Enables correct field-name resolution on `Option<Struct>` values combined via `??`; previously fell into the documented "array-of-structs field misread" fallback landmine referenced in the surrounding comments. |
| `50.mir/_MirLoweringExpr/expr_dispatch.spl:2735-2742` | bare `Struct` (`.exists`/`?.`-chain, struct-name provenance) | REVIEW | Same class of fix as above for the `ExistsCheck` handling path. |

**Not part of this collision family (checked, excluded):** `module_check.spl:122-150,359-381`
bare `case Function(func):`/`case Struct(struct_def):`/etc. match `compiler.frontend.ast.Node`'s
own payload-carrying variants (a different enum, a different bug family — the "always-true
naked-struct-pattern" one already documented at `hir_lowering/expressions.spl:416-426`), not
`SymbolKind`. Confirmed by tracing `item: Node` in the enclosing `register_definition` signature.

## Counts

- **SAFE:** 1 (`get_all_functions`)
- **REVIEW:** 14 (all rows above except the 2 `Variable`-only control rows, which are not part of
  the 11-variant collision at all and are excluded from the count)
- **BROKEN:** 0 confirmed; 1 suspected pending follow-up (see below)

## Test verification (per campaign's `Results:`-only rule)

```
env -u SIMPLE_TIMEOUT_SECONDS timeout 400 bin/simple test --no-session-daemon <spec> ...
```

| Spec | Result |
|---|---|
| `test/01_unit/compiler/semantics/resolve_spec.spl` | `Results: 1 total, 1 passed, 0 failed` |
| `test/02_integration/compiler/static_method_desugar_spec.spl` | `Results: 3 total, 3 passed, 0 failed` |
| `test/feature/usage/static_method_resolution_spec.spl` | `Results: 11 total, 11 passed, 0 failed` |
| `test/01_unit/compiler/hir/symbol_table_all_functions_spec.spl` | `Results: 2 total, 2 passed, 0 failed` |
| `test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl` | `Results: 3 total, 3 passed, 0 failed` |
| `test/01_unit/compiler/interpreter/static_method_overload_dispatch_spec.spl` | `Results: 4 total, 4 passed, 0 failed` |
| `test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl` | `Results: 21 total, 1 passed, 20 failed` |

### Observed test regression — `vhdl_design_catalog_spec.spl` (20/21 failing)

All 20 failures report `semantic: type mismatch: cannot cast dict to i64`, in test cases named
around "recovers hardware metadata from the driver source sidecar" / "rejects ambiguous
normalized metadata aliases" — i.e. the **hardware-metadata-sidecar** feature area, not the
`rebase`/type-identity path this audit flagged (rows above at lines 365-369/636-647). No
mechanistic link from the flagged `Struct | Enum` arms to a "dict cast to i64" error was found in
the time available (the `rebase: Dict<i64,i64>` variable these arms populate is already
`i64`-keyed/valued, so a widened dict→i64 cast failure doesn't obviously originate there).

This file also carries **pre-existing uncommitted WIP from another session**
(`git status` shows it modified; `git diff` shows only cosmetic positional-bind renames —
`FuncPtr(signature)`→`FuncPtr(inner_sig)`, `Call(dest, func, args)`→`Call(dest, callee, args)`,
`CallTerminator(..., func, ...)`→`CallTerminator(..., callee, ...)` around lines 105-185 — none of
which touch the flagged 365-369/636-647 arms). **Not attributed to this audit's arms** with any
confidence; flagged as an open item for whichever lane owns `vhdl_design_catalog.spl`/its spec —
do not assume it is caused by PTR1/PTR2 without further isolation.

## Risk verdict

1. **`resolve_strategies.spl:304-314` (`is_static_method_call`)** — highest blast radius. Every
   `Type.method()` call in the whole compiler was silently routed through instance-method
   resolution instead of static-method resolution until PTR1/PTR2 landed. All directly-relevant
   specs pass (18/18 across 3 specs), which is reassuring but not exhaustive — this predicate sits
   on the hot path of `resolve_expr`, called for literally every method call HIR-resolved.
2. **`value_struct_layout.spl:20-23` / `validate_value_struct_layouts`** — highest severity-if-wrong.
   A hard compile-error-emitting safety gate (by-value struct cycle rejection) that has never fired
   once in this codebase's history is now live in 3 driver call sites (normal build, bootstrap,
   and one more phase) with **zero test coverage** anywhere in `test/`. Could either (a) correctly
   catch a real latent infinite-recursion/stack-overflow hazard for the first time, or (b) false-
   positive-reject a currently-compiling program that has a superficially cycle-shaped but actually
   safe by-value struct graph. No regression observed in the specs run this lane, but none of them
   specifically target this function.
3. **`method_calls_literals.spl:906-918` → `:2293-2295`/`:2312-2318` static-method MIR-lowering
   fallback chain** — a second, independent static-dispatch code path (this time in MIR lowering,
   downstream of #1) that was entirely dead and is now reachable, with real codegen side effects
   (`emit_resolved_direct_call`, return-type override). Passing static-method specs exercise this,
   but the fallback is specifically a *fallback* — i.e. it only fires when the primary
   `struct_method_syms`-keyed lookup misses, a narrower and less-tested slice of the input space.

No source fix was applied by this lane: every arm found is either functioning correctly now that
it fires (the intended PTR1/PTR2 payoff) or is a genuine behavior change with passing test
evidence, not an "obviously wrong" arm meeting the BROKEN bar. The one candidate BROKEN signal
(`vhdl_design_catalog_spec.spl`) could not be attributed to these arms within this lane's budget
and is left as an open follow-up rather than guessed at.
