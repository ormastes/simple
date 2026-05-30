# PERF BUG: Interpreter 1460x slower than C on recursive workloads

**Date:** 2026-05-18
**Status:** RESOLVED 2026-05-27 -- non-regression / expected tree-walking interpreter cost
**Severity:** Medium (interpreter-only; native Cranelift is 1.6x C)
**Benchmark:** fib(30) — C -O2: 8ms, Cranelift native: 13ms, Interpreter: 11,680ms

## Resolution

This tracker is closed as a performance-roadmap item rather than an active bug.
The measured native Cranelift result is already within the expected compiled
language range for the cited benchmark, and the interpreter result matches the
current tree-walking architecture. Closing this report does not claim bytecode,
JIT, or broad string-clone optimization work has landed; those are larger
design projects and should be tracked as feature/performance roadmap work if
they are prioritized.

## Analysis

Tree-walking interpreter overhead on recursive fib:
- Each function call: hash lookup for function name, argument binding, stack frame creation
- Each expression: recursive eval with pattern match on AST node type
- No JIT, no bytecode compilation

## Already Optimized
- debug_state() AtomicBool fast-path (pre-existing, commit 51c85da213)
- MIR inliner: borrow-first + expanded allowlist (pre-existing, commit 51c85da213)
- ISA cache: Cranelift AOT reuses Arc<TargetIsa> across compilation units (pre-existing, commit 51c85da213)
- Extern dispatch: 1080-arm match → HashMap with OnceLock (commit fca3f29b05, this session)

## Remaining Optimization Targets
1. **Value::Str(String) → Arc<str>** — eliminate deep copies on clone. Estimated 15-25% on string-heavy workloads. Large refactor (hundreds of callsites).
2. **Expression cascade** — 5-stage discriminant re-check in `interpreter/expr.rs:182-220`. Estimated 5-10%.
3. **Bytecode compilation** — compile AST to flat bytecode before execution. Would reduce interpreter overhead by 10-50x but is a major project.
4. **Cranelift JIT for hot functions** — detect hot paths and JIT-compile them. Would close remaining gap to C.

## Verdict
- **Native Cranelift**: No perf bug — 1.6x C is within Go/Rust/Swift range
- **Interpreter**: Expected gap for tree-walking design. Not a regression, but Value::Str Arc<str> refactor would help string-heavy real programs
