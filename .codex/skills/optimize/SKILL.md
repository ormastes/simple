---
name: optimize
description: Optimize Simple code and performance-sensitive paths using SPipe evidence and the in-repo Simple OptimizerPlugin surfaces. Use when asked to make Simple as fast as C/Go, run performance checks, remove unused logic/data, apply optimizer-plugin guidance, or improve algorithms without changing language, behavior, or user code semantics.
metadata:
  short-description: Semantics-preserving Simple optimization
---

# Simple Optimization Workflow

Use this skill for performance work. Keep the work in Simple unless the user
explicitly asks for runtime/compiler C/Rust changes.

## Hard Rules

- Preserve behavior and public API. Add or keep SPipe coverage before risky rewrites.
- Do not rewrite the feature in C/Rust to win a benchmark.
- Prefer algorithm/data-layout improvements over micro-tuning.
- For concurrency benchmarks, keep `thread_spawn`, `cooperative_green_spawn`,
  and `multicore_green_spawn` separate. Optimize the Pure Simple path first and
  use the cross-language profile rows as evidence instead of replacing Simple
  code with Rust/C. For `multicore_green_spawn`, require
  `MulticoreGreenHandle.used_runtime_pool()` evidence before treating a row as
  Go-like M:N CPU parallelism.
- Remove unused logic/data only when it is proven unused by tests, references, or
  optimizer/lint evidence.
- Do not change user-visible inputs, outputs, ordering, errors, or persistence
  formats for speed unless requirements explicitly allow it.
- If C/Go parity is not reachable in Simple because of a runtime/compiler
  blocker, record a concrete bug under `doc/08_tracking/bug/`.

## Required Loop

1. Establish baseline: run the relevant existing perf/spec script first.
2. Run the optimizer app on touched `.spl` files:
   `bin/simple run src/app/optimize/main.spl <file> --full --level=O3`.
   Use `simple optimize <file> --full --level=O3` only after the local binary
   exposes the top-level command. Use `--compare` only when the file is a
   runnable benchmark/program.
3. For source-pattern work, inspect or update the legacy scanner at
   `src/compiler/90.tools/perf/optimizer.spl`, but do not rely on it as the
   primary CLI while `simple optimize` is available.
4. Inspect plugin architecture before adding optimizer infrastructure:
   `src/compiler/60.mir_opt/optimizer_plugin.spl` and
   `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`.
5. Optimize in this order:
   algorithmic complexity, allocation/copy removal, data layout, loop hoisting,
   dispatch reduction, then small local cleanup.
6. Rerun correctness tests and the same perf script. Compare before/after numbers.

## C-Level Target

For C/Go parity requests, use C/Go as an evidence target, not as an
implementation language. Acceptable outcomes are:

- Simple meets or beats the target with unchanged behavior.
- Simple improves but misses the target; record the remaining bottleneck and a
  measured blocker.
- The benchmark was unfair or measured different semantics; fix the harness and
  document the model difference.

## SPipe Expectations

- Add SPipe tests for any optimized path whose behavior could regress.
- Perf specs belong under `test/05_perf/`; generated/manual docs belong under
  `doc/06_spec/test/05_perf/`.
- Use real assertions. No `pass_todo`, empty examples, or trivial always-true
  assertions.
