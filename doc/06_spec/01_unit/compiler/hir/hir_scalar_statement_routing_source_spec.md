# HIR Scalar Statement Routing Source Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

### HIR scalar statement routing source contract

#### classifies only the existing tuple Val and Var marker

- Inspect the shared multi-lowering predicate.
- Expected: Val and Var use the existing `len() > 1` plus `"("` prefix marker.
- Expected: the change does not impose a new closing-parenthesis rule on malformed AST input.

#### classifies every final scalar statement by its lowered HIR kind

- Inspect value-block scalar and lowered-HIR tail routing.
- Expected: every non-tuple source statement is lowered exactly once to a fresh scalar HIR statement.
- Expected: final For, While, Loop, Break, Continue, Yield, Throw, With, and ordinary expression statements are classified by `HirStmtKind`, not by their source variant.
- Expected: final HIR expressions become the block value except `Return`, which remains a statement.
- Expected: assignments and every other non-expression HIR statement remain statements.
- Expected: no source-expression discriminator gate can hide an expression-producing statement variant.

#### uses the same split in bootstrap and ordinary unit blocks

- Inspect both unit-block lowering loops.
- Expected: ordinary statements call `lower_hir_stmt` directly.
- Expected: only classified tuple statements call `lower_hir_stmt_multi` and splice their results.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / HIR |
| Status | Active, not executed in this change |
| Source | `test/01_unit/compiler/hir/hir_scalar_statement_routing_source_spec.spl` |
| Updated | 2026-08-25 |
| Generator | Manually synchronized source contract |

## Performance Contract

The common statement path remains linear in source statements and emitted HIR
statements. It removes the temporary singleton `[HirStmt]`, its indexed reload,
and its one-element splice loop. Tuple destructuring retains its existing
linear expansion, left-to-right evaluation, error behavior, and output order.
