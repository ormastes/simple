# Formal Verification: Rust Implementations

Part of [Formal Verification](formal_verification.md).

### 1. Borrow State (`src/common/src/manual.rs`)

**Dynamic representation** (maps directly to Lean):
```rust
pub struct BorrowState {
    pub exclusive: bool,
    pub shared: usize,
}

impl BorrowState {
    pub fn is_valid(&self) -> bool;  // exclusive → shared = 0
    pub fn take_exclusive(&mut self) -> bool;
    pub fn take_shared(&mut self) -> bool;
    pub fn release_exclusive(&mut self);
    pub fn release_shared(&mut self);
}
```

**Type-safe representation** (invariant encoded in type):
```rust
/// Invalid states are unrepresentable
pub enum ValidBorrowState {
    Unborrowed,                        // no borrows
    Exclusive,                         // one exclusive borrow
    Shared(NonZeroUsize),             // one or more shared borrows
}

impl ValidBorrowState {
    pub fn take_exclusive(self) -> Result<Self, Self>;
    pub fn take_shared(self) -> Result<Self, Self>;
    pub fn release_exclusive(self) -> Self;
    pub fn release_shared(self) -> Self;
}
```

Lean equivalent:
```lean
inductive ValidBorrowState
  | unborrowed
  | exclusive
  | shared (count : Nat) (h : count > 0)
```

### 2. GC State (`src/common/src/manual.rs`)

```rust
pub struct GcState {
    live: HashSet<usize>,
    borrowed: HashSet<usize>,
}

impl GcState {
    pub fn is_safe(&self) -> bool;     // borrowed ⊆ live
    pub fn allocate(&mut self) -> usize;
    pub fn borrow(&mut self, id: usize) -> bool;
    pub fn release(&mut self, id: usize);
    pub fn collect_safe(&mut self, id: usize) -> bool;
}
```

### 3. MIR Lowerer State (`src/compiler/src/mir/lower.rs`)

**Explicit state machine** (instead of implicit `Option<T>` fields):
```rust
pub enum LowererState {
    Idle,
    Lowering {
        func: MirFunction,
        current_block: BlockId,
        loop_stack: Vec<LoopContext>,
    },
}

pub struct LoopContext {
    pub continue_target: BlockId,
    pub break_target: BlockId,
}
```

Lean equivalent:
```lean
inductive LowererState
  | idle
  | lowering (func : MirFunction) (block : BlockId) (loops : List LoopContext)
```

**State transitions are explicit**:
```rust
fn begin_function(&mut self, func: MirFunction) -> Result<()>;  // Idle → Lowering
fn end_function(&mut self) -> Result<MirFunction>;              // Lowering → Idle
fn set_current_block(&mut self, block: BlockId) -> Result<()>;
fn push_loop(&mut self, ctx: LoopContext) -> Result<()>;
fn pop_loop(&mut self) -> Result<LoopContext>;
```

### 4. Effect Tracking (`src/compiler/src/mir/types.rs`)

**Effect System for Async Safety:**

The effect system tracks which operations may block, enabling compile-time verification that async-safe functions are truly non-blocking.

**Lean-matching types (for formal verification):**
```rust
// Matches AsyncCompile.lean exactly (Rust uses "async" naming)
pub enum AsyncEffect { Compute, Io, Wait }

pub fn is_async(e: AsyncEffect) -> bool {  // Lean: is_async
    !matches!(e, AsyncEffect::Wait)
}

pub fn pipeline_safe(es: &[AsyncEffect]) -> bool {  // Lean: pipelineSafe
    es.iter().all(|e| is_async(*e))
}
```

**Production types (combined for practical use):**
```rust
pub enum Effect {
    Compute,   // Pure computation - always async-safe
    Io,        // Non-blocking I/O - async-safe (may yield but won't block)
    Wait,      // Blocking wait - NOT async-safe (forbidden in async functions)
    GcAlloc,   // GC allocation (forbidden in nogc mode, but async-safe)
}

impl Effect {
    /// Returns true if this effect is async (non-blocking).
    pub fn is_async(&self) -> bool;   // !matches!(self, Effect::Wait)
    pub fn is_nogc(&self) -> bool;       // !matches!(self, Effect::GcAlloc)
    pub fn to_async(&self) -> AsyncEffect;  // Convert to Lean-matching type
}

pub struct EffectSet {
    effects: Vec<Effect>,
}

impl EffectSet {
    /// Check if all effects are async (no blocking waits).
    pub fn is_pipeline_safe(&self) -> bool;  // ∀e. is_async(e)
    pub fn is_nogc(&self) -> bool;           // ∀e. is_nogc(e)
    pub fn append(&mut self, other: &EffectSet);
}
```

**AST Effect Annotations (`src/parser/src/ast.rs`):**
```rust
pub enum Effect {
    Async,  // async fn - non-blocking, async-safe function
}
```

### 5. Call Target with Effects (`src/compiler/src/mir/types.rs`)

**Precise effect tracking for function calls**:
```rust
pub enum CallTarget {
    Pure(String),        // No side effects
    Io(String),          // I/O but non-blocking
    Blocking(String),    // May block (wait, join, recv)
    GcAllocating(String), // Allocates on GC heap
}

impl CallTarget {
    pub fn effect(&self) -> Effect;
    pub fn from_name(name: &str) -> Self;  // Lookup known functions
}
```

MIR instructions use CallTarget:
```rust
pub enum MirInst {
    Call { dest: Option<VReg>, target: CallTarget, args: Vec<VReg> },
    GcAlloc { dest: VReg, ty: TypeId },  // Explicit GC allocation
    Wait { dest: Option<VReg>, target: VReg },  // Explicit blocking
    // ... other instructions
}

impl HasEffects for MirInst {
    fn effect(&self) -> Effect;
}
```

### 6. Pure Type Inference (`src/type/src/lib.rs`)

```rust
pub enum SimpleTy {
    Nat, Bool, Str,
    Generic(String, Vec<SimpleTy>),
    Arrow(Box<SimpleTy>, Box<SimpleTy>),
}

pub enum SimpleExpr {
    LitNat(i64), LitBool(bool), LitStr(String),
    Add(Box<SimpleExpr>, Box<SimpleExpr>),
    Generic(String, Vec<SimpleExpr>),
    IfElse(Box<SimpleExpr>, Box<SimpleExpr>, Box<SimpleExpr>),
    Lam(Box<SimpleExpr>),
    App(Box<SimpleExpr>, Box<SimpleExpr>),
}

/// Pure, total inference function
pub fn infer_simple(expr: &SimpleExpr) -> Option<SimpleTy>;

/// The Lean model proves `tyEq`/`listTyEq` reflect `Ty` equality, so the
/// boolean equality checks in `ifElse`/`app` stay sound even for generics.
```

## Simplification Guidelines

If a model proves too complex to mirror the implementation:

1. **Use type-safe encodings**: Replace dynamic validation (`is_valid()`) with types that make invalid states unrepresentable (`ValidBorrowState`).

2. **Make state machines explicit**: Replace `Option<T>` with `enum State { Idle, Active(T) }` to document valid transitions.

3. **Factor invariants into local predicates**: Use simple predicates (`borrowed ⊆ live`, `exclusive → shared = 0`) that compose algebraically.

4. **Prefer total functions**: Use `Option<T>` return types rather than panics or partial relations.

5. **Tag effects explicitly**: Mark operations with their effect category (`Compute`, `Io`, `Wait`, `GcAlloc`) so compile-time checks become membership tests.

6. **Separate blocking and allocation**: Use explicit `Wait` and `GcAlloc` MIR instructions instead of inferring from call names.

## Verification Levels

| Model | Rust Type | Invariant | Encoding | Purpose |
|-------|-----------|-----------|----------|---------|
| manual_pointer_borrow | `ValidBorrowState` | `exclusive ⊕ shared` | Type-safe enum | Memory safety |
| gc_manual_borrow | `GcState` | `borrowed ⊆ live` | Runtime check | GC safety |
| async_compile | `EffectSet` | `∀e. is_async(e)` | List property | Async safety (no blocking) |
| nogc_compile | `EffectSet` | `∀e. is_nogc(e)` | List property | Real-time safety |
| type_inference | `SimpleTy` | determinism | Pure function | Type soundness |
| mir_lowerer | `LowererState` | state machine | Explicit enum | Correct compilation |
| block_builder | `BlockBuildState` | `Open → Sealed` | State machine | IR construction |
| actor_lifecycle | `ActorLifecycle` | `Running → Joined` | State machine | Actor safety |
| type_allocator | `TypeIdAllocator` | monotonic allocation | Pure allocator | ID uniqueness |
| visibility | `Visibility` | `Public ⊕ Private` | Type-safe enum | Access control |
| mutability | `Mutability` | `Mutable ⊕ Immutable` | Type-safe enum | Mutability tracking |
| move_mode | `MoveMode` | `Move ⊕ Copy` | Type-safe enum | Closure capture |
| special_enum | `SpecialEnumKind` | `Option ⊕ Result` | Type-safe enum | Built-in enum handling |
| builtin_class | `BuiltinClass` | `Range ⊕ Array` | Type-safe enum | Built-in class dispatch |
| method_lookup | `MethodLookupResult` | `Found ⊕ NotFound ⊕ MissingHook` | Type-safe enum | Method dispatch |
| execution_mode | `ExecutionMode` | `Normal ⊕ Actor ⊕ Generator ⊕ Context` | State machine | Interpreter context |
| special_names | `METHOD_*`, `FUNC_*`, `ATTR_*` | String constants | Named constants | Magic string elimination |

## Remaining Simplification Opportunities

(All identified simplifications have been completed.)

---

Next: [Simplifications](formal_verification_simplifications.md)
