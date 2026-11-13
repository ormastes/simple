# Seed interpreter: one-line `if c: a else: b` now pays the statement-`if` cost

- **Date:** 2026-11-14
- **Status:** OPEN (perf, P3)
- **Area:** Rust bootstrap seed, tree-walking interpreter (`exec_if_core`,
  `interpreter_control.rs`; tail handling in `interpreter/block_exec.rs`)
- **Found:** review of work/covfix-20261113 (seed parser change in
  `parser/src/stmt_parsing/control_flow.rs`: a statement-position one-line
  if/else now parses to the spanned `Node::If` the block form produces, so
  line coverage can attribute it).

## Measurement

`fib(28)`, interpreter (`SIMPLE_EXECUTION_MODE=interpret`), coverage off,
15 interleaved runs, user CPU seconds (mean), seeds built at c89479c9d7b (base)
and the branch head:

| body | base | branch |
|---|---|---|
| block form `if n < 2:` / `n` / `else:` / `fib(..)+fib(..)` | 1.452 | 1.457 |
| one-line `if n < 2: n else: fib(..)+fib(..)` | 1.414 | 1.449 |

The block-form row isolates the branch's extra tail `record_node_coverage`
call: noise. The one-line row is +2.5%. It now costs the same as the block form,
because it runs through `exec_if_core` (a block scope per arm) and no longer
through the cheaper `Expr::If` evaluation. This is a worst-case micro-benchmark
(every call is a tail one-liner); real programs dilute it.

## Fix direction

Give `exec_if_core` a fast path for an arm whose block is a single
`Node::Expression` that declares nothing: evaluate it without pushing a block
scope. That would speed up the block form too. Pin it with an interpreter A/B on
the two rows above.
