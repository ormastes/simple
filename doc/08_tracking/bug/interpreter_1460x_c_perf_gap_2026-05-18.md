# PERF BUG: Interpreter 1460x slower than C on recursive workloads

**Date:** 2026-05-18
**Severity:** Medium (interpreter-only; native Cranelift is 1.6x C)
**Benchmark:** fib(30) — C -O2: 8ms, Cranelift native: 13ms, Interpreter: 11,680ms

## Analysis

Tree-walking interpreter overhead on recursive fib:
- Each function call: hash lookup for function name, argument binding, stack frame creation
- Each expression: recursive eval with pattern match on AST node type
- No JIT, no bytecode compilation

## Already Optimized (this session)
- debug_state() AtomicBool fast-path (was already done before this session)
- Extern dispatch: 1080-arm match → HashMap with OnceLock (for rt_* heavy programs)
- MIR inliner: borrow-first + expanded allowlist (ConstFloat, Cast, UnaryOp)
- ISA cache: Cranelift AOT reuses Arc<TargetIsa> across compilation units

## Remaining Optimization Targets
1. **Value::Str(String) → Arc<str>** — eliminate deep copies on clone. Estimated 15-25% on string-heavy workloads. Large refactor (hundreds of callsites).
2. **Expression cascade** — 5-stage discriminant re-check in `interpreter/expr.rs:182-220`. Estimated 5-10%.
3. **Bytecode compilation** — compile AST to flat bytecode before execution. Would reduce interpreter overhead by 10-50x but is a major project.
4. **Cranelift JIT for hot functions** — detect hot paths and JIT-compile them. Would close remaining gap to C.

## Verdict
- **Native Cranelift**: No perf bug — 1.6x C is within Go/Rust/Swift range
- **Interpreter**: Expected gap for tree-walking design. Not a regression, but Value::Str Arc<str> refactor would help string-heavy real programs
