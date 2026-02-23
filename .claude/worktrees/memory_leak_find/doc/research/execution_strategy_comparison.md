# Execution Strategy Comparison: Interpreter vs Compiler vs JIT

**Date:** January 2026
**Status:** Research Complete
**Related:** `codegen_backend_comparison.md`, `backend_test!` macro in `test_helpers.rs`

---

## 1. Standard Model (Textbook)

| Feature | Interpreter | Compiler (traditional) | JIT Compiler |
|---------|-------------|----------------------|--------------|
| When compilation occurs | Never | Before execution | During execution |
| Output | Direct execution | Native binary | Native code cache |
| Startup time | Very fast | Fast | Slower (warm-up) |
| Peak performance | Slow | Good | Often best (adaptive) |
| Portability | High | Recompile per platform | High (bytecode) |
| Memory overhead | Low | Lower at runtime | Higher (runtime compiler + profiler) |
| Runtime optimization | No | No | Yes (profile-based) |

### Interpreter

Reads and executes source code (or bytecode) instruction-by-instruction without producing a native binary. Fast edit-run cycle, simple to implement, portable. Slower runtime due to per-instruction dispatch overhead.

### Compiler (Traditional / "AOT")

Translates to native machine code before execution. This is the classic compiler model (C, C++, Rust, Go). The term "AOT" is mainly used in JIT-centric ecosystems (JVM, .NET) to distinguish from their default JIT path. For languages that were always compiled, it is simply "the compiler."

### JIT (Just-in-Time)

Compiles at runtime, typically from bytecode. Identifies hot code paths and optimizes selectively. Best long-running performance via profile-guided optimization. Warm-up overhead and higher memory use.

---

## 2. Simple Language Implementation

Simple has three **independent, non-adaptive** backends selected at invocation time:

```
Source Code
    |
    v
  Parser
    |
    v
   AST ──────────────────── Interpreter (jitless, tree-walking)
    |                              |
    v                              v
   HIR                        Exit Code
    |
    v
   MIR ──────── JIT (Cranelift in-memory native)
    |                   |
    |                   v
    |              Exit Code
    |
    └────────── Compiler (Cranelift -> Object -> SMF -> Executable)
                        |
                        v
                   Exit Code
```

### 2.1 Interpreter (`RunningType::Interpreter`) -- Jitless

- **Type:** AST tree-walking interpreter, **no JIT, no bytecode, no compilation**
- **Pipeline:** Source -> Parser -> AST -> evaluate directly
- **Feature coverage:** 100% of language features
- **Location:** `src/rust/compiler/src/interpreter_eval.rs` (+ 14 related files)
- **Key point:** Purely interpreted. No native code generated at any point. This is a jitless interpreter in every sense -- it walks the AST and dispatches on node type.

### 2.2 JIT (`RunningType::Compiler`) -- In-Memory Native

- **Type:** Whole-program JIT (compiles everything at startup, not selective/adaptive)
- **Pipeline:** Source -> AST -> HIR -> MIR -> Cranelift JIT -> in-memory native code -> call
- **Feature coverage:** Partial (no closures, enums, complex collections yet)
- **Fallback:** `InterpCall`/`InterpEval` MIR instructions call back to interpreter for unsupported features
- **Location:** `src/rust/compiler/src/codegen/jit.rs`
- **Key point:** This is JIT in the sense that it compiles to native code in-memory at runtime. But it is **not adaptive** -- it compiles the whole program once, with no profiling or hot-code detection.

### 2.3 Compiler (`RunningType::CompileAndRun`) -- Traditional Compiler

- **Type:** Traditional compiler producing a native executable (what some ecosystems call "AOT")
- **Pipeline:** Source -> AST -> HIR -> MIR -> Cranelift Object -> SMF -> Settlement + Loader -> Executable -> spawn process
- **Feature coverage:** Same as JIT (shares Cranelift codegen backend)
- **Output:** SMF (Simple Module Format) executable on disk
- **Location:** `src/rust/compiler/src/codegen/cranelift.rs`
- **Key point:** This is just a compiler. It produces a binary, you run the binary. Same as `gcc foo.c -o foo && ./foo`. The "AOT" label is unnecessary here -- Simple is not a JIT-first language that added ahead-of-time as an alternative. This is the standard compiled path.

### 2.4 Verification Modes

- `RunningType::Both` -- runs Interpreter + JIT, asserts results match
- `RunningType::All` -- runs Interpreter + JIT + Compiler, asserts results match
- `RunningType::Wasm` -- WebAssembly via Wasmer (feature-gated)

---

## 3. Corrected Terminology for Simple

The textbook uses "AOT" vs "JIT" because JIT-based runtimes (JVM, CLR, V8) were first, and "AOT" was added later as an optimization. Simple's history is different: it started with an interpreter and added compilation. The correct framing:

| RunningType | Better Name | Analogy |
|-------------|------------|---------|
| `Interpreter` | **Jitless interpreter** | CPython, Ruby MRI |
| `Compiler` (JIT) | **In-memory compiler** (JIT) | LuaJIT, Cranelift JIT |
| `CompileAndRun` | **Compiler** (traditional) | GCC, Rustc, Go |

The interpreter has **no JIT component whatsoever**. It is purely jitless. The JIT mode is a separate, independent backend -- not a layer on top of the interpreter.

---

## 4. Comparison: Simple vs Standard Model

### 4.1 Matches

| Aspect | Standard Model | Simple |
|--------|---------------|--------|
| Interpreter: no compilation | Executes directly | AST tree-walking, no native code |
| Compiler: binary before run | `gcc`-style compile then run | Cranelift -> SMF executable |
| JIT: native at runtime | In-memory native code | Cranelift JIT in-memory |
| Interpreter: full features | Dynamic dispatch handles all | 100% language coverage |
| Compiler: standalone binary | No runtime dependency | SMF executable runs independently |

### 4.2 Differences

| Aspect | Standard JIT Model (JVM, V8) | Simple | Impact |
|--------|------------------------------|--------|--------|
| **Architecture** | Bytecode VM + adaptive JIT | Three independent backends, no bytecode | Simpler; no shared IR between interpreter and compiler |
| **Interpreter type** | Bytecode interpreter (compact dispatch) | AST tree-walker (no bytecode) | Higher per-node overhead; but simpler implementation |
| **JIT trigger** | Hot-code profiling at runtime | Whole-program at startup | No warm-up but no adaptive optimization |
| **Adaptive optimization** | Profile-guided recompilation | None; static opt levels (`speed`/`size`/`none`) | Predictable but misses runtime-specific speedups |
| **Tiered compilation** | Interpreter -> baseline -> optimizing | Single tier chosen upfront | No gradual optimization |
| **Fallback direction** | Deoptimize: native -> interpreter | `InterpCall`: native -> interpreter (for missing features) | Same direction but different purpose (deopt vs feature gap) |
| **JIT scope** | Selective (hot methods only) | Whole-program (all functions) | Higher compile time, simpler implementation |
| **Interpreter + JIT mixing** | Same process, tiered | Separate modes; JIT can fallback to interp via `InterpCall` | Not mixed by default; fallback is explicit |

### 4.3 Architectural Comparison

```
Standard JIT (JVM HotSpot):
  Source -> Bytecode -> Bytecode Interpreter -> [profile] -> JIT (hot paths) -> Native
                                                  ^                              |
                                                  └── deoptimize ───────────────┘

Simple (three independent paths):
  Source -> AST -> Interpreter                       (jitless, full features)
  Source -> AST -> HIR -> MIR -> JIT                 (in-memory native, partial features)
  Source -> AST -> HIR -> MIR -> Compiler -> Binary  (traditional compile, partial features)
                               \
                                └─ InterpCall fallback for unsupported ops
```

Key difference: Standard JIT systems **start interpreted and promote** hot code to native. Simple **chooses one path** at startup. Compiled code can **fall back** to the interpreter for missing features (`InterpCall`), but this is for feature gaps, not deoptimization.

---

## 5. What Simple Could Gain

### 5.1 Bytecode Layer (Medium Value)

Adding bytecode between AST and execution would:
- Speed up the interpreter (compact dispatch vs tree-walking)
- Enable bytecode serialization (faster startup for large programs)
- Share one IR between interpreter and compiler

Trade-off: Significant effort; current AST interpreter is adequate.

### 5.2 Adaptive/Tiered JIT (High Value, High Effort)

Start in interpreter, profile, JIT-compile hot functions:
- Best throughput for long-running programs
- Requires profiling infrastructure, deoptimization, runtime complexity

Trade-off: Only worthwhile for server workloads. Not aligned with Simple's current goals.

### 5.3 Selective JIT (Medium Value)

Compile only called functions instead of whole program:
- Reduces JIT compile time
- Natural extension of existing `InterpCall` fallback

Trade-off: Needs per-function dispatch decisions.

### 5.4 Code Caching (Low-Medium Value)

Cache compiled native code across runs (like V8's code cache):
- Eliminates repeated compilation
- Trade-off: Invalidation complexity; Simple programs are typically short-lived

---

## 6. Simple's Unique Strengths

### 6.1 Verification Mode

`RunningType::Both` and `RunningType::All` run the same program on multiple backends and assert identical results. Uncommon in production implementations. The `backend_test!` macro extends this to per-backend test granularity:

```rust
backend_test!(my_test, interp_jit, "main = 42", 42);
// Generates: my_test_interpreter, my_test_jit
```

### 6.2 Interpreter Fallback from Compiled Code

`InterpCall`/`InterpEval` MIR instructions let compiled code call back to the jitless interpreter for features not yet supported by codegen. This enables incremental codegen development without blocking language features.

### 6.3 Shared Codegen Backend

Both JIT and Compiler use `CodegenBackend<M>` generic over Cranelift module type:
- `CodegenBackend<JITModule>` for JIT (in-memory)
- `CodegenBackend<ObjectModule>` for Compiler (object file)

Same codegen logic, different output targets.

---

## 7. Summary

Simple's three backends map to the standard model as follows:

| Simple | Standard Term | Description |
|--------|--------------|-------------|
| Interpreter | Jitless interpreter | AST tree-walking, no compilation at all |
| JIT | Non-adaptive JIT | Whole-program in-memory compilation via Cranelift |
| Compiler | Traditional compiler | Produces native executable (like GCC/Rustc) |

The "AOT" label is misleading for Simple's compiler mode -- it is simply a compiler. "AOT" implies a contrast with a default JIT path (as in JVM/CLR). Simple does not have a default JIT path; the interpreter is jitless and the compiler is just a compiler.

Key architectural differences from the standard JIT model:
- **No bytecode** -- separate AST interpreter and MIR-based compiler paths
- **No adaptive optimization** -- mode chosen upfront, predictable behavior
- **No tiered compilation** -- single tier per invocation
- **Reverse fallback** -- compiled code falls back to interpreter for feature gaps (not deoptimization)

---

## References

- Simple compiler: `src/rust/compiler/src/codegen/` (JIT, Compiler)
- Simple interpreter: `src/rust/compiler/src/interpreter_eval.rs`
- Simple driver: `src/rust/driver/src/interpreter.rs` (RunningType dispatch)
- Backend test infra: `src/rust/driver/tests/test_helpers.rs` (Backend enum, backend_test! macro)
- Related research: `doc/research/codegen_backend_comparison.md`
