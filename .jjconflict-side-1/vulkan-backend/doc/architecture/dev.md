# Architecture: Development Guide

Part of [Architecture Overview](architecture.md).

### Adding a New Feature: Checklist

```
1. [ ] Is this syntax? → parser/ only
2. [ ] Is this types? → type/ only
3. [ ] Is this evaluation? → compiler/interpreter*.rs
4. [ ] Is this a new pointer/handle? → common/ trait, runtime/ impl, compiler/ wrapper
5. [ ] Is this cross-module? → common/ contract first
6. [ ] Does it need GC? → Use GcAllocator trait, NOT GcRuntime directly
```

### Feature → Module Mapping

| Feature Category | Modify | DON'T Modify |
|-----------------|--------|--------------|
| New syntax (keywords, operators) | `parser/` | compiler, runtime |
| New AST nodes | `parser/ast.rs` | anywhere else |
| Type system additions | `type/lib.rs` | compiler/interpreter |
| New Value variants | `compiler/value.rs` | common/, driver/ |
| Builtin methods | `compiler/interpreter_method.rs` | driver/ |
| Builtin functions | `compiler/interpreter_call.rs` | driver/ |
| New pointer kinds | `common/manual.rs` + `compiler/value.rs` wrapper | driver/ |
| Actor features | `common/actor.rs` contract + impl | compiler (uses only) |
| GC features | `common/gc.rs` trait + `runtime/memory/` impl | compiler (uses only) |
| IO/stdlib | `lib/` | compiler/, runtime/ |
| Hot reload | `loader/registry.rs` | compiler/, driver/ |
| Package management | `pkg/` | compiler/, runtime/ |
| Runtime FFI functions | `runtime/value/` | compiler/ (imports only) |
| Generator state machine | `compiler/mir/generator.rs` + `runtime/value/async_gen.rs` | driver/ |
| Module system parsing | `parser/` (tokens, AST, statements) | compiler/ (stubs only) |
| Project configuration | `compiler/project.rs` | driver/, runtime/ |
| Module resolution | `compiler/module_resolver.rs` | driver/, parser/ |

### Example: Adding a New Builtin Method (e.g., `array.sum()`)

```rust
// 1. ONLY modify compiler/interpreter_method.rs
// 2. Find the array method dispatch section
// 3. Add the new method:

"sum" => {
    let sum = arr.iter()
        .filter_map(|v| v.as_int().ok())
        .sum::<i64>();
    Ok(Value::Int(sum))
}

// DON'T:
// - Add this to driver/
// - Create a new file
// - Modify common/
```

### Example: Adding a New Pointer Kind

```rust
// Step 1: Define in common/manual.rs
pub struct NewPtr<T> { ... }

// Step 2: Create wrapper in compiler/value.rs
pub struct NewPtrValue {
    ptr: NewPtr<Value>,  // Uses generic from common
}

// Step 3: Add Value variant in compiler/value.rs
pub enum Value {
    // ...
    NewPtr(NewPtrValue),
}

// Step 4: Handle in interpreter (evaluate_expr, etc.)

// DON'T:
// - Put NewPtrValue in common/
// - Create multiple wrapper implementations
```

### Cross-Module Communication Rules

```
┌─────────────────────────────────────────────────────────────┐
│ If module A needs to call module B:                         │
│                                                             │
│ 1. Define trait in common/                                  │
│ 2. B implements trait                                       │
│ 3. A uses trait, not B directly                             │
│                                                             │
│ Example: compiler → GC                                      │
│ - common/gc.rs: trait GcAllocator                          │
│ - runtime/memory/gc.rs: impl GcAllocator for GcRuntime     │
│ - compiler/pipeline.rs: fn with_gc(gc: Arc<dyn GcAllocator>)│
└─────────────────────────────────────────────────────────────┘
```

## Logging Strategy (cross-cutting)
- Use `tracing` for structured, span-based logging; init once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- Use `#[tracing::instrument]` to capture entry/exit/args with minimal overhead—this is the closest to AOP weaving Rust offers.
- Prefer spans with fields (`tracing::info_span!(...)`) over ad-hoc prints; keep logging opt-in for perf-sensitive paths.
- Rust has no runtime AOP; lean on proc-macros and DSL transforms if we need cross-cutting concerns.

---

## Formal Verification (Lean 4)

The `verification/` directory contains Lean 4 proofs for key safety invariants. Each model has a corresponding Rust implementation that exactly matches the Lean definitions.

### Model-Implementation Correspondence

| Model | Lean Project | Rust Location | Verified Properties |
|-------|--------------|---------------|---------------------|
| **Manual Pointer Borrow** | `manual_pointer_borrow/` | `common/manual.rs` | Borrow operations preserve validity |
| **GC Manual Borrow** | `gc_manual_borrow/` | `common/manual.rs` | GC collection preserves borrowed ⊆ live |
| **Async Compile (Async Safety)** | `async_compile/` | `compiler/mir/types.rs` | Non-blocking functions compose safely |
| **NoGC Compile** | `nogc_compile/` | `compiler/mir/types.rs` | NoGC programs compose safely |
| **Type Inference** | `type_inference_compile/` | `type/lib.rs` | Type inference is deterministic |

### Building Proofs

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build individual proof
cd verification/manual_pointer_borrow && lake build

# All proofs verified with Lean 4.x
```

### Rust Types Matching Lean

```rust
// common/manual.rs - matches ManualPointerBorrow.lean
pub struct BorrowState { pub exclusive: bool, pub shared: Nat }
pub fn take_exclusive(s: BorrowState) -> BorrowState { ... }
pub fn borrow_state_valid(s: &BorrowState) -> bool { ... }

// compiler/mir/types.rs - matches AsyncCompile.lean (Async Safety)
// AsyncEffect tracks which operations may block (Wait = blocking, others = non-blocking)
pub enum AsyncEffect { Compute, Io, Wait }  // Wait = blocking operation
pub fn is_async(e: AsyncEffect) -> bool { !matches!(e, AsyncEffect::Wait) }  // Lean: is_async
pub fn pipeline_safe(es: &[AsyncEffect]) -> bool { es.iter().all(|e| is_async(*e)) }

// type/lib.rs - matches TypeInferenceCompile.lean
pub enum LeanTy { Nat, Bool, Arrow(Box<LeanTy>, Box<LeanTy>) }
pub fn lean_infer(expr: &LeanExpr) -> Option<LeanTy> { ... }
```

See `doc/formal_verification.md` for detailed correspondence tables and proofs.

---

## Refactoring Plan (grounded in current code)
- **Stabilize the memory boundary**: keep `simple_common::gc::GcAllocator` the only compiler/runtime contract; re-export `GcRuntime`/`NoGcAllocator` from `runtime::memory` and thread selection through the driver via config/env without leaking Abfall or manual allocators across crates.
- **Introduce a MIR/CFG layer in `compiler`**: lower parsed AST into a stable, borrow-checkable IR to host alias analysis, region checks, and later optimizations. Keep this IR independent of runtime details so features like borrowing or async safety (async) checks stay local.
- **Isolate pointer-kind semantics in `common`**: move any new borrow/region markers or handle pool ABI types into `common` and keep parser/runtime unaware of each other; compiler should translate to these markers only.
- **Module hygiene in runtime**: keep GC backends under `runtime::memory::{gc,no_gc}` and pool/concurrency in separate submodules; avoid cross-imports so swapping GC or introducing arenas does not affect the scheduler.
- **Diagnostics pipeline**: add a small error-reporting helper crate or module consumed by parser/type/borrow passes so new analyses (borrow checker, effects) can emit consistent spans without coupling passes together.
- **Driver simplification**: keep watch/build/run orchestration in `driver` using published interfaces only (`compiler::CompilerPipeline`, loaders, `runtime::memory` selection) to avoid circular reach as new features land.

---

Back to: [Architecture Overview](architecture.md)
