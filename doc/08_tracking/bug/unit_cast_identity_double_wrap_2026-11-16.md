# `u as Unit` double-wraps a value that is already that unit (pure-Simple HIR)

Found in review of PR #9585, 2026-11-16. `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`
lowered every `x as Name` (Name a declared `unit`) to `StructLit(Name, [("value", x)])`.
When `x` is already of type `Name` this builds `Name { value: Name {...} }`; the seed
passes the value through unchanged.

## Fix (lane rb4-unitwrap)

Before building the record, the cast reads the operand's HIR type (or its declared
type via `cast_operand_declared_type`); if it is `Named` with the same `SymbolId`
as the target, the operand is returned as-is. Nested `((n as U) as U) as U` is
covered because the inner StructLit carries `has_type_: true`.

Spec: `test/01_unit/compiler/unit_from_primitive_construction_spec.spl`
(`unit cast of a value that is already that unit`: i64, f64, nested).
Limit: the pure-Simple path cannot run on the deployed seed (which also predates
#9585, so the whole spec fails there, 0/8); not natively verified.

Status: verification-pending
