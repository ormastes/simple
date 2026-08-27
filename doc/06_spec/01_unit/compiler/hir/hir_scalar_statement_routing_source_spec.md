# HIR Scalar Statement Routing Source Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

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

#### keeps the exact bootstrap compile-source selector scalar through HIR and MIR

- Read the live `bootstrap_compile_option_takes_value` and
  `bootstrap_compile_source_from_args` definitions from
  `src/app/cli/bootstrap_main.spl` and lower them in bootstrap mode.
- Expected: bootstrap-mode environment setup and exact restoration both
  succeed through the non-raw environment facade, including unset restoration.
- Expected: HIR lowering reports zero errors and the direct option helper exists
  with a `Bool` return.
- Expected: `bootstrap_compile_source_from_args` exists with a `Str` return.
- Expected: HIR retains the `While`, the loop-local `Let` initialized by
  `Index(args, i)`, and the terminal empty-string scalar block value.
- Expected: MIR reports zero errors (therefore neither `E-MIR-TYPE-Unknown` nor
  `E-SFFI-016`) and its authoritative `type_transport_receipts` count is zero.

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
The live fixture extraction and lowering are linear in the selected source;
the production selector itself remains O(n) in argument count with O(1)
auxiliary state. The test necessarily owns an O(n) source string and compiler
IR, so it makes no constant-memory claim for the fixture harness.
