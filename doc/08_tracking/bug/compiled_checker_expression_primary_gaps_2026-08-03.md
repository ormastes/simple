# Compiled checker expression/primary parser gaps

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Claimed by: `stage4_expr_batch`
- Date: 2026-08-03
- Frozen compiler/checker evidence:
  `/tmp/simple-stage4-b1df.WmYLW6/build/mini_builds/current-checker-cycle4`
- Owner boundary: pure-Simple expression/primary parsing only; declaration parsing,
  type parsing, and HIR module resolution are excluded.

## Frozen scope

The batch owns ten checker-failing inventory rows grouped by shared expression
roots:

- contextual named argument `pass:`: `source-000024`, `source-000151`,
  `source-000152`, `source-000153`;
- image/custom literal `img{...}`: `source-000078`;
- caret/xor expression: `source-000245`;
- prefix raw-pointer dereference: `source-000202`, `source-000248`;
- `unsafe:` expression block: `source-000201`;
- `is Type` test: `source-000030`.

`source-000203` and `source-000204` are fixed-array type declarations, not
uninitialized-array expressions, and remain assigned to the type-parser batch.
The frozen inventory contains no `[_; N]` expression row.

## Acceptance

1. Reproduce all ten rows before edits with the frozen compiled checker.
2. Fix shared parser owners rather than changing repository consumers.
3. Add exact, adjacent, and malformed/recovery coverage per root cause.
4. Retry only the originally failed rows once after the fix.
5. Do not weaken invalid-syntax diagnostics or change declaration/HIR owners.

## Resolution evidence

The current-main checker rebuilt from the admitted pure-Simple Stage 3 compiler
in 14.7 seconds (47 compiled, zero failed; 415,620 KiB peak RSS). The one
failed-only retry clears nine whole files. `source-000201` clears its original
line-44 `unsafe:` diagnostic and advances to a distinct line-57
`asm volatile:` indented-block diagnostic, now tracked separately as
`compiled_checker_asm_volatile_indent_gap_2026-08-03`.

An executable focused probe compiles 52 modules with zero failures and exits
zero. It covers exact, adjacent, malformed, and recovery cases while asserting
the rich bridge shapes for `UnaryOp.Deref`, `BinOp.Is`, `BinOp.BitXor`, and
`ExprKind.CustomBlock(kind, BlockValue.Raw(payload))`. The permanent coverage
is `test/01_unit/compiler/parser/expression_primary_parity_spec.spl`.
