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


## 2026-11-09 — FIXED on work/p3-subj4-seed-20261109

Acceptance met: seed semantic errors raised while evaluating a
statement/expression now carry the file and line (column: statement start)
of the offending node, and a cargo test pins the formatted output.

Output before: `error: semantic: variable 'nope_undefined' not found`
Output after (fresh cargo build of release/1.0.0 source):

```
error: semantic: sem_err.spl:2:5: variable `nope_undefined` not found      (module level)
error: semantic: sem_err2.spl:2:5: variable `missing_name` not found       (inside a function body)
```

Mechanism: statement-execution loop heads in the interpreter record the
current node's span in a thread-local (`CURRENT_NODE_SPAN`);
`CompileError::semantic_with_context` adopts it and `get_current_file()`
when the raise site recorded no position; `Display` renders
`semantic: <file>:<line>:<col>: <message>`.

Cargo pin: `src/compiler_rust/compiler/tests/semantic_error_position.rs`
(2 tests, both executed GREEN 2026-11-09).

Known limitation: the `Expr` enum carries no span, so the position is
statement-granularity; plain `CompileError::Semantic(String)` raise sites
(non-contextual) are not covered by this change.
