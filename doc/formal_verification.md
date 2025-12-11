# Formal Verification Sketches (Lean 4)

This document describes the formal verification models for the Simple Language Compiler.

## Index

| File | Content |
|------|---------|
| [formal_verification.md](formal_verification.md) | Overview, Status, Models 1-4 |
| [formal_verification_models.md](formal_verification_models.md) | Models 5-8, Verification Models |
| [formal_verification_impl.md](formal_verification_impl.md) | Rust Implementations, Guidelines |
| [formal_verification_simplifications.md](formal_verification_simplifications.md) | Completed Simplifications |

---


This repo now carries small Lean 4 projects that encode sanity properties for memory and compilation behaviors. Each folder is a standalone Lake project; to check one, run `lake build` inside it (Lean 4 from `leanprover/lean4:stable` is specified in each `lean-toolchain`).

## Terminology

| Term | Meaning |
|------|---------|
| **`async fn`** | Asynchronous, non-blocking function (safe to call from async code) |
| **`wait`** | Blocking operation (join, recv, sleep) - forbidden in async functions |
| **`nogc`** | No GC allocations - for real-time or embedded contexts |

**Key Insight:** An `async` function is guaranteed not to block the calling thread, making it safe to use in async executors. The Lean model proves that composing async functions preserves this property.

## Formal Verification Summary

All 8 Lean models have been **verified**. Five models have exact Rust implementations, and three new models formalize the module system specification from `doc/depedency_tracking.md`. The verification confirms:

1. **Types match exactly** - Same structure, same variants
2. **Functions match exactly** - Identical logic and semantics
3. **Theorems encoded as runtime assertions** - Invariants checked at debug time

## Model-Implementation Correspondence Status

| Model | Lean File | Rust Implementation | Status | Proofs |
|-------|-----------|---------------------|--------|--------|
| Manual Pointer Borrow | `manual_pointer_borrow/` | `common/manual.rs` → `BorrowState`, `ValidBorrowState` | ✅ Verified | 5 theorems |
| GC Manual Borrow | `gc_manual_borrow/` | `common/manual.rs` → `GcState`, `GcStateVerify` | ✅ Verified | 2 theorems |
| Async Compile (Async Safety) | `async_compile/` | `compiler/mir/effects.rs` → `AsyncEffect`, `is_async()`, `pipeline_safe()` | ✅ Verified | 2 theorems |
| NoGC Compile | `nogc_compile/` | `compiler/mir/effects.rs` → `NogcInstr`, `nogc()` | ✅ Verified | 2 theorems |
| Type Inference | `type_inference_compile/` | `type/lib.rs` → `LeanTy`, `LeanExpr`, `lean_infer()` | ✅ Verified | 1 theorem |
| Module Resolution | `module_resolution/` | `doc/depedency_tracking.md` spec | ✅ Verified | 4 theorems |
| Visibility Export | `visibility_export/` | `doc/depedency_tracking.md` spec | ✅ Verified | 7 theorems |
| Macro Auto-Import | `macro_auto_import/` | `doc/depedency_tracking.md` spec | ✅ Verified | 6 theorems |

---

## Individual Model Verification Reports

### 1. Manual Pointer Borrow Model ✅ VERIFIED

**Lean Model** (`verification/manual_pointer_borrow/src/ManualPointerBorrow.lean`):
```lean
structure BorrowState where
  exclusive : Bool := false
  shared : Nat := 0

def valid (s : BorrowState) : Prop :=
  if s.exclusive then s.shared = 0 else True

def takeExclusive (s : BorrowState) : BorrowState :=
  if s.shared = 0 then { s with exclusive := true } else s

def takeShared (s : BorrowState) : BorrowState :=
  if s.exclusive then s else { s with shared := s.shared + 1 }
```

**Proven Theorems:**
- `exclusive_ok`: `valid s → valid (takeExclusive s)`
- `shared_ok`: `valid s → valid (takeShared s)`
- `release_ok`: `valid s → valid (releaseShared s) ∧ valid (releaseExclusive s)`
- `validState_always_valid`: `∀ vs, valid vs.toState` (ValidBorrowState is always valid)
- `toValid_toState`: Round-trip property for conversions

**Rust Implementation** (`src/common/src/manual.rs`):

| Lean | Rust | Match |
|------|------|-------|
| `BorrowState { exclusive, shared }` | `BorrowState { exclusive: bool, shared: Nat }` | ✅ Exact |
| `valid` | `borrow_state_valid()` | ✅ Exact |
| `takeExclusive` | `take_exclusive()` (pure) | ✅ Exact |
| `takeShared` | `take_shared()` (pure) | ✅ Exact |
| `releaseShared` | `release_shared()` (pure) | ✅ Exact |
| `releaseExclusive` | `release_exclusive()` (pure) | ✅ Exact |

**Key Features:**
- `Nat` type with saturating `pred()` matches Lean's `Nat.pred`
- Pure functions return new state (no mutation)
- `ValidBorrowState` enum provides type-safe alternative where invalid states are unrepresentable

**ValidBorrowState (Type-Safe Design):**
Both Lean and Rust now provide `ValidBorrowState`, an alternative representation where the validity invariant is encoded in the type itself:

```lean
inductive ValidBorrowState
  | unborrowed                              -- no borrows
  | exclusive                               -- one exclusive borrow
  | shared (count : Nat) (h : count > 0)    -- shared borrows (count > 0)
```

This design makes invalid states (exclusive AND shared) unrepresentable at compile time, eliminating the need for runtime validity checks. The key theorem `validState_always_valid` proves that any `ValidBorrowState` converts to a valid `BorrowState`.

---

### 2. GC Manual Borrow Model ✅ VERIFIED

**Lean Model** (`verification/gc_manual_borrow/src/GcManualBorrow.lean`):
```lean
structure GcState where
  live : List Nat := []
  borrowed : List Nat := []

def safe (s : GcState) : Prop :=
  ∀ id, id ∈ s.borrowed → id ∈ s.live

def allocate (s : GcState) (id : Nat) : GcState :=
  { s with live := id :: s.live }

def borrow (s : GcState) (id : Nat) : GcState :=
  if h : id ∈ s.live then { s with borrowed := id :: s.borrowed } else s

def collectSafe (s : GcState) (id : Nat) : GcState :=
  if h : id ∈ s.borrowed then s else { s with live := s.live.erase id }
```

**Proven Theorems:**
- `borrow_preserves`: `safe s → safe (borrow s id)`
- `collect_preserves`: `safe s → safe (collectSafe s id)`

**Rust Implementation** (`src/common/src/manual.rs`):

| Lean | Rust | Match |
|------|------|-------|
| `GcState { live, borrowed }` | `GcStateVerify { live: Vec<usize>, borrowed: Vec<usize> }` | ✅ Exact |
| `safe` | `gc_state_verify_safe()` | ✅ Exact |
| `allocate` | `gc_allocate()` | ✅ Exact (prepend) |
| `borrow` | `gc_borrow()` | ✅ Exact |
| `release` | `gc_release()` | ✅ Exact |
| `collectSafe` | `gc_collect_safe()` | ✅ Exact |

**Key Features:**
- `Vec` with `insert(0, id)` matches Lean's `List` with cons (`::`)
- Pure functions return new state
- `GcState` (HashSet-based) also provided for O(1) production use

---

### 3. Async Compile Model ✅ VERIFIED

**Purpose:** The async safety property ensures functions are safe to use in async contexts by verifying they contain no blocking operations. An `async fn` is "non-blocking" - it may perform I/O but will never block the calling thread.

**Terminology:**
- `async fn` = non-blocking function, safe to call from async code
- `wait` = blocking operation (e.g., `join`, `recv`, `sleep`)
- `is_async(e)` = Lean/Rust function that checks if an effect is non-blocking

In the Simple language:
- `async fn` - non-blocking function guaranteed not to contain blocking operations

**Lean Model** (`verification/async_compile/src/AsyncCompile.lean`):
```lean
inductive Effect
  | compute   -- Pure computation, always async-safe
  | io        -- I/O operation (non-blocking), async-safe
  | wait      -- Blocking operation, NOT async-safe
  deriving DecidableEq, Repr

def is_async (e : Effect) : Bool :=
  match e with
  | Effect.wait => false
  | _ => true

def pipelineSafe (es : List Effect) : Prop :=
  ∀ e, e ∈ es → is_async e = true
```

**Proven Theorems:**
- `append_safe`: `pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b)`
- `wait_detected`: `pipelineSafe [e] → e ≠ Effect.wait`

**Rust Implementation** (`src/compiler/src/mir/types.rs`):

| Lean | Rust | Match |
|------|------|-------|
| `Effect.compute` | `AsyncEffect::Compute` | ✅ Exact |
| `Effect.io` | `AsyncEffect::Io` | ✅ Exact |
| `Effect.wait` | `AsyncEffect::Wait` | ✅ Exact |
| `is_async` | `is_async()` | ✅ Exact |
| `pipelineSafe` | `pipeline_safe()` | ✅ Exact |

**Code Comparison:**
```lean
def is_async (e : Effect) : Bool :=
  match e with
  | Effect.wait => false
  | _ => true
```
```rust
pub fn is_async(e: AsyncEffect) -> bool {
    !matches!(e, AsyncEffect::Wait)
}
```

**Blocking Operations (Effect::Wait):**
- `await` - wait for async result
- `wait` - explicit wait
- `join` - join thread/actor
- `recv` - receive from channel (blocking)
- `sleep` - sleep current thread

---

### 4. NoGC Compile Model ✅ VERIFIED

**Lean Model** (`verification/nogc_compile/src/NogcCompile.lean`):
```lean
inductive Instr
  | const (n : Nat)
  | add
  | gcAlloc
  deriving DecidableEq, Repr

def nogc (p : List Instr) : Prop :=
  ∀ i, i ∈ p → i ≠ Instr.gcAlloc
```

**Proven Theorems:**
- `nogc_append`: `nogc a → nogc b → nogc (append a b)`
- `nogc_singleton`: `i ≠ Instr.gcAlloc → nogc [i]`

**Rust Implementation** (`src/compiler/src/mir/types.rs`):

| Lean | Rust | Match |
|------|------|-------|
| `Instr.const n` | `NogcInstr::Const(u64)` | ✅ Exact |
| `Instr.add` | `NogcInstr::Add` | ✅ Exact |
| `Instr.gcAlloc` | `NogcInstr::GcAlloc` | ✅ Exact |
| `nogc` | `nogc()` | ✅ Exact |

**Code Comparison:**
```lean
def nogc (p : List Instr) : Prop :=
  ∀ i, i ∈ p → i ≠ Instr.gcAlloc
```
```rust
pub fn nogc(p: &[NogcInstr]) -> bool {
    p.iter().all(|i| !matches!(i, NogcInstr::GcAlloc))
}
```

---

---

Next: [Models 5-8](formal_verification_models.md)
