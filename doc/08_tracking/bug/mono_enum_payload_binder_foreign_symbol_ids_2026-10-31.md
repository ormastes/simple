# 40.mono stamps enum payload binders with the declaring module's symbol ids

- Date: 2026-10-31
- Area: `src/compiler/40.mono/monomorphize_integration.spl` (`collect_generics`, `bind_payload_pattern`, `rewrite_expr` Var/NamedVar)
- Surfaces as: MIR `enum match expression and retained Result/Optional declarations conflict` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, `enum_match_subject_type`) in the stage3 self-host build; 14 modules in rev8 (`$S/phase3/rev8-s3-build.log`), e.g. `src/compiler/35.semantics/narrowing.spl:486`, `src/compiler/20.hir/generated/hir_visitor.spl:188,303`.
- Spec: `test/01_unit/compiler/mono/mono_enum_payload_binder_relocation_spec.spl`

## Symptom

With `SIMPLE_RTI_DIAGNOSTICS=1`:

```
enum match expression and retained Result/Optional declarations conflict;
  expression=optional(struct(compiler.frontend.parser_types_expr::Block)[]);
  retained=optional(struct(compiler.hir.hir_definitions::HirBlock)[])
  at src/compiler/35.semantics/narrowing.spl:486
```

The subject is always a depth-1 enum-pattern binder whose payload type is declared in another module (`HirExprKind.If(_, then_, else_: HirBlock?)` from `compiler.hir.hir_definitions`). The retained (MIR local) type is right. The "expression" type names whatever symbol the CONSUMER's table holds at the same raw id, so it varies with the consumer and, when the consumer's id allocation order changes, between runs (`MirVariantDef`, `MockDecl`, `ModuleSurfaceComposite`, ... for the same `hir_visitor.spl:303`).

## Root cause

1. `collect_generics` records `enum_payload_types["{Enum}::{Variant}::{slot}"] = <declared payload HirType>` from the declaring module's `HirEnum`. The `Named` ids inside that `HirType` belong to the declaring module's `SymbolTable`. No owner module was recorded.
2. `bind_payload_pattern` preferred that row over the binder's own `pat.type_`, although HIR lowering had already typed the binder in the consumer's id space (`expression_components.spl`, `imported_surface_type`).
3. `rewrite_expr` stamps `env_type(symbol)` onto each read of the binder that carries no concrete type of its own (`has_type_ = true`), unrelocated. The sibling `Field` arm transports its type with `relocate_mono_types`; the Var arm did not.
4. MIR's `enum_match_expr_type` trusts `expr.type_` first (presence bit), then compares it with the retained local declaration and refuses the match.

Small probes rarely show it because the consumer's and provider's raw ids for the payload struct can coincide; the 490-module closure (`$S/mirfix/retained-red-all.log`) and the full stage3 closure show it reliably.

## Fix

- `enum_payload_owner_modules[key] = module_name` beside each `enum_payload_types` write.
- `bind_payload_pattern`: a concrete `pat.type_` (consumer-local) wins; a declared row is bound only through `bind_payload_declared_type`, which transports it from the owner module into `current_module` with `relocate_mono_types` (identity when owner == consumer or the type has no nominal part). A failed transport leaves the binder to the untyped fallbacks (and E-MONO-042 names the site).

## Not a fix

`work/mir-retained-20261031` commit f70ccfb5bd1 (`enum_match_subject_is_plain_local`) returns the retained type whenever the keys disagree for a plain local. That hides the wrong `expr.type_` from this one check only; the stamped type still reaches every other `enum_match_expr_type` consumer and mono's own inference, and it would also accept a genuine conflict. Do not land it.
