# Seed: semantic errors are reported without file:line:col

- **Date**: 2026-11-09
- **Status**: open
- **Area**: compiler_rust (seed interpreter diagnostics)
- **Split from**: `seed_optional_query_comparison_divergence_2026-08-16.md` § "Divergence C"
  (owner decision 2026-11-09: split C into its own bug; not fixed in the parent).

## Problem

The seed prints semantic errors as `error: semantic: <message>` with no source
position, while the self-hosted compiler prints
`<file>:<line>:<col>: error: semantic: <message>`. Divergences A and B of the
parent bug presented as runtime mysteries for this reason.

## Acceptance

- A seed semantic error raised while evaluating a statement/expression carries
  the file and line (column where the AST has it) of the offending node.
- Cargo test in `src/compiler_rust/compiler/tests/` pins the formatted output.
