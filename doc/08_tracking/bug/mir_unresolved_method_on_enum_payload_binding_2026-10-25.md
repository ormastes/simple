# MIR: method call on enum-payload binding lowers to const-0 (silent null)

- Date: 2026-10-25
- Found in: stage3 build (rebuilt stage2 compiling `bootstrap_main`), `build/s3-bis-new/build.log`
- Severity: high — wrong code shipped in the stage3 binary (call result = 0), exit 0

## Symptom
`[mir-lower] WARNING: unresolved method call '<m>' lowered to const-0 placeholder (silent-null risk, Task #145)`
x36: supports/cost/preferred_vector_width_bits (6 each), format (6), size_bytes/alignment (3 each),
get_symbol_id (2), to_compiled_module, description, as_str, to_text.

## Cause
MIR lowering resolves a method receiver through `receiver_declared_type` /
`find_local_hir_type`. A binding introduced by an enum-match payload pattern has
no remembered HIR type when:
1. the variant has >=2 slots (`case Add(l, r)`, `case Array(elem, size)`,
   `case RequiresUnsafe(op, _)`, `case MethodCall(.., resolution)`): the
   multi-slot bind path decoded the slot but never called
   `remember_local_hir_type` (the single-slot path does);
2. single-slot payloads whose type is not recovered (`TargetCapsKind.X86(caps)`
   trait-impl receivers; `Ok(output)` of a trait-object `compile_module` call);
3. `for e in <payload array>` element locals.

## Sites (source workarounds, tag `WA-MIR-UNRESOLVED-<method>`)
| method | site |
|---|---|
| supports / cost / preferred_vector_width_bits | `src/compiler/70.backend/feature_caps_arch32.spl` caps_kind_* |
| format | `src/compiler/30.types/dim_constraints.spl` DimExpr.format Add/Mul/Div |
| size_bytes / alignment | `src/compiler/50.mir/mir_types.spl` MirType.size_bytes/alignment |
| get_symbol_id | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (2) |
| description | `src/compiler/35.semantics/unsafe.spl` UnsafeError.message |
| to_compiled_module | `src/compiler/70.backend/backend/backend_api.spl` CompilerBackend.compile |
| as_str, to_text | NOT localized — warning carried no location. Now prints `module=`; re-read next stage3 log. |

Each WA routes the call through a typed-parameter free function, which the
current stage2 resolves.

## Compiler fix
`switch_operators_calls.spl` multi-slot bind path now calls
`remember_local_hir_type(bound_slot, declared slot type)`. Cases 2/3 remain open.
Remove WAs once a stage2 with the fix shows zero warnings for these sites.

## Related: native `d[k]` on Dict<text, bool> yields int 1/0 (found via #4504)
Native codegen returns the raw word for a bool-valued dict index read, typed as
i64 rather than bool. Truthiness (`if d[k]:`) is unaffected; explicit
comparisons / formatting / storing into bool fields can be. `src/compiler`
explicit-compare sites: `10.frontend/core/interpreter/module_loader_core.spl`
:239, :643, :927, :934 (`d[k] == true`) and
`90.tools/leak_check/static_runner.spl:221` (array, not dict). ~609 bool-valued
dict declarations exist in `src/compiler`; not audited individually. Open.

## Follow-up: duplicate struct layouts and wrong-enum match arms (2026-10-25)

- **Field-layout collision** (`JoinPoint`, `CostEstimate`, `Diagnostic`, `CompileError`,
  `TextSpan`, `ElfSymbol`, `CollectionPlanFacts`): `struct_field_order` is keyed by bare
  name and first-registration wins. `resolve_field_index`
  (`50.mir/_MirLowering/function_lowering.spl`) already tries the module-qualified
  `composite_layout_key` first; now the bare tiers fail closed — a bare name flagged in
  `struct_field_order_conflict_warned` is skipped in the value-provenance tier and is a
  fatal error (not first-pick) in the final name tier.
- **`AsmConstraintKind` has no variant `Tuple`/`Struct`**: in
  `40.mono/monomorphize_integration.spl` (`rewrite_enum_payload`,
  `mono_relevant_expr_v1`) the `Some(p)` binding of a `HirEnumPayload?` gets a wrong
  recorded scrutinee type (cross-module SymbolId collision, same class as this bug), and
  the bare `case Tuple/Struct` arms were resolved by global owner search. Arms are now
  qualified as `HirEnumPayload.Tuple/Struct`. The payload-binding type inference itself
  remains the open root cause above.
