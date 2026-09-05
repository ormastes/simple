# Math Block Lowering Analysis — scilib Port

**Phase:** 2-research  
**Date:** 2026-04-27  
**Author:** Research Agent (Claude Sonnet)  
**Scope:** Can existing `math{}` handle linalg + ndarray + df operators, or do we need new blocks?

---

## 1. What `math{}` Currently Parses and Lowers To

### 1.1 Architecture: String-Payload Runtime Interpreter

`math{}` is **not** a syntax extension into the HIR pipeline. It is a string-payload runtime interpreter with its own lexer → parser → AST → eval stack, completely bypassing HIR.

The entry points are:

- `src/compiler_rust/compiler/src/blocks/mod.rs:99` — `"m" | "loss" | "nograd" => MathBlock.evaluate(payload)`
- `src/compiler_rust/compiler/src/blocks/math/mod.rs:76-86` — `evaluate_with_env(payload, interpreter_env)` bridges the surrounding Simple `Env` into the math evaluator by converting `Value::Int/Float/Array` into `MathValue` heuristics

The interpreter's variable bridge (`eval/mod.rs:116-177`) converts `Value::Array` → `MathValue::Tensor` by shape-sniffing: 1D if all elements are scalars, 2D if all elements are same-length arrays. Ragged arrays and 3D+ nesting silently return `None` and are excluded from the math scope.

### 1.2 MathExpr AST — What Exists

`src/compiler_rust/compiler/src/blocks/math/ast.rs` defines the full AST:

| Node | Covers |
|------|--------|
| `Int(i64)`, `Float(f64)`, `Array(Vec<MathExpr>)` | Literals including nested 2D matrix |
| `Add/Sub/Mul/Div/Pow/Mod` | Binary arithmetic |
| `Neg/Abs` | Unary |
| `App(String, Vec<MathExpr>)` | All functions: `matmul`, `dot`, `transpose`, `reshape`, `zeros`, `ones`, `eye`, `mean`, `sum`, `std`, `relu`, `sigmoid`, `softmax`, `sum(i,1..n)` |
| `Subscript(Box<MathExpr>, Box<MathExpr>)` | Single-index: `A[i]` only |
| `Sum/Prod/Integral` | Binder forms |
| `Eq/Neq/Lt/Le/Gt/Ge/Approx` | Comparisons |

### 1.3 Tensor Runtime

The tensor implementation at `src/compiler_rust/compiler/src/blocks/math/tensor/` covers:

- `matrix.rs`: `matmul` (2D×2D), `dot` (1D·1D), `transpose`  
- `indexing.rs`: point-access `get(indices: &[usize])` and `set` only — no slice range  
- `broadcast.rs`: NumPy-style broadcasting for element-wise ops  
- `reduction.rs`: `sum`, `mean`, `var`, `std`, `argmin`, `argmax` — no `axis` parameter  
- `elementwise.rs`: `relu`, `sigmoid`, `tanh`, `softmax`  
- `creation.rs`: `zeros`, `ones`, `eye`, `arange`, `linspace`, `rand`, `randn`

Backend selection (`backend/auto_select.rs`) dispatches by **expression complexity score** (number of tensor ops, estimated element count), not by Simple types.

---

## 2. Gap Analysis by Domain

### 2.1 Linalg: `A @ B`, `A + B`, `A * c`, `A.T`, `inv(A)`, `solve(A, b)`, broadcasting

| Operation | Status | Gap |
|-----------|--------|-----|
| `A + B` elementwise | Works via `binary_op` + broadcasting | None |
| `A * c` scalar broadcast | Works via `binary_op` broadcast | None |
| `matmul(A, B)` | Works — `eval/mod.rs:391` | Syntax: no infix `@` token (`ast.rs` has no `MatMul` variant; `lexer.rs` has no `@` token) |
| `A @ B` | Fails silently or parse error | AST variant missing; lexer token missing |
| `A.T` postfix property | Fails — `App("T", [])` not dispatched as postfix | `MathExpr` has no method-call or property node |
| `transpose(A)` | Works — `eval/mod.rs:393` | Usability only |
| `inv(A)` | Missing | No `inv` in `is_builtin_function` (`ast.rs:119-160`) or `eval_function` (`eval/mod.rs:365-466`) |
| `solve(A, b)` | Missing | Same — no LAPACK route from math block |
| Broadcasting | Works for `+`, `-`, `*`, `/` | `eval/tensor_broadcasting.rs` present |

**Verdict for linalg:** Core operations work via `App` form. The ergonomic `@` operator and `.T` shorthand require parser/AST additions. `inv` and `solve` require both AST entries and a LAPACK FFI backend call from within the interpreter.

### 2.2 Ndarray: `A[i:j, k]`, `A.reshape(s)`, `A + B` elementwise, `A.sum(axis=0)`

| Operation | Status | Gap |
|-----------|--------|-----|
| `A[i]` 1D index | Works — `eval/mod.rs:283-308` | None |
| `A[i][j]` chained | Works — reduces row then re-indexes | Verbose |
| `A[i:j]` slice range | Missing | `Subscript` node only holds single `MathExpr`; no `Slice` AST node; no `:` token in math lexer |
| `A[i:j, k]` multi-axis slice | Missing | Same; also no multi-index subscript |
| `A.reshape(s)` method call | Works as `reshape(A, s)` | No method-call syntax; `MathExpr` has no `MethodCall` node |
| `A + B` elementwise | Works via broadcasting | None |
| `A.sum()` (full) | Works as `sum(A)` — `eval/mod.rs:410` | No method form |
| `A.sum(axis=0)` | Missing | `eval_sum_tensor` at `eval/mod.rs:410` has no axis parameter |

**Verdict for ndarray:** Index-by-integer works. Slicing is the main parser gap: the `Subscript` node (`ast.rs:48`) holds only one index expression. Axis-parameterised reductions require a new keyword-argument form or a multi-arg function `sum(A, axis=0)` convention.

### 2.3 Df: `df['col']`, `df['a'] + df['b']`, `df.groupby('k').sum()`

| Operation | Status | Gap |
|-----------|--------|-----|
| `df['col']` string index | Fails | `Subscript` eval at `eval/mod.rs:283-308` requires `MathValue::Tensor` + `MathValue::Int`; string key is not handled |
| `df['a'] + df['b']` | Fails | Depends on the above |
| `df.groupby('k').sum()` | Fails completely | Method-chaining + string args + lambda grouping: no representation in `MathExpr` |
| Value bridge | Missing | `value_to_math_value` (`eval/mod.rs:131`) has no DataFrame/Series conversion path |

**Verdict for df:** `math{}` cannot handle DataFrame operations. The mismatch is fundamental: `MathExpr` is a numeric expression tree; DataFrames are labeled columnar stores requiring string-keyed indexing, method chaining, groupby aggregators, and join operations. These are not math expressions in the symbolic sense.

---

## 3. Type-Directed Lowering Hooks

**The core architectural limit:** `math{}` does **not** see Simple's type system. Backend selection is done at runtime by `backend/auto_select.rs`, which inspects `ExprComplexity` (a heuristic count of tensor operations and estimated element count), not the static type of variables bridged from the Simple scope.

This means:

- **Runtime probe (Phase 1, cheap):** When `A @ B` is evaluated and `A` is already a `MathValue::Tensor` with dtype `f64` and ndim=2, the evaluator can check at call time and dispatch via the Torch/CUDA backend hook. This works within the existing architecture — the backend selection already runs at `eval/mod.rs:85-99`, and `BackendCapability::for_backend(CUDA).supports_tensor = true`. The gap is that `@` isn't tokenized yet.

- **Compile-time HIR dispatch (Phase 2, expensive):** If the arch requires that `A: NDArray<Float64>` in scope statically selects a cuBLAS kernel at codegen time — bypassing the runtime evaluator — then `math{}` must be rebuilt as a proper HIR syntactic form, not a string-payload block. That is a major architectural change of the compiler with no existing precedent.

**Open question for Phase 3 architect:** Does "lower into the underlying CUDA Fortran backend" (state.md line 13) mean runtime dispatch (current hook can be extended) or compile-time lowering (forces HIR lift)? This is the single most consequential decision for the whole math-block extension plan.

---

## 4. The `loss{}`/`nograd{}` Precedent

`loss{}` and `nograd{}` are **aliases only** — `blocks/mod.rs:99` dispatches all three to `MathBlock.evaluate(payload)` and `blocks/mod.rs:77` dispatches all three display calls to `MathBlock.display_string`. They share the same parser, AST, eval, and backend selection verbatim.

This precedent establishes that adding a new block keyword is **trivially cheap** (one match arm in two switch statements) when the new block reuses `math{}` semantics. It is **non-trivial** only when the new block diverges in parser behaviour or return type.

---

## 5. Recommendation

### 5.1 Path

**Hybrid:** Extend `math{}` for linalg and ndarray. Keep df outside all math blocks as pure stdlib.

| Domain | Path | Rationale |
|--------|------|-----------|
| Linalg (`@`, `A.T`, `inv`, `solve`) | Extend `math{}` parser + AST | Shares tensor infrastructure; `@` is one lexer token + one AST variant; `inv`/`solve` are two new `App` dispatch arms with LAPACK FFI calls |
| Ndarray (slicing, axis reductions) | Extend `math{}` parser + AST | `Slice` node + `:` token + multi-index `Subscript`; axis param via `sum(A, 0)` function convention |
| Df (`df['col']`, `groupby`) | Pure Simple stdlib — no block | Fundamental semantic mismatch; force-fitting into `MathExpr` would require rebuilding the entire AST |

If ergonomics warrant separate block keywords (`linalg{}`, `array{}`), they can be added as zero-cost aliases pointing to the extended `MathBlock` — but only after the parser work is done. The separate keywords buy no compiler capability; they only scope user intent.

### 5.2 Concrete Compiler Changes Required

**Parser/Lexer** (`blocks/math/lexer.rs`, `parser.rs`):
- Add `@` token → `MathToken::At`
- Add `:` slice token → `MathToken::Colon` (already used in binder `..` range — must not collide)
- Parse `A @ B` at multiplicative precedence level (between `Mul` and `Pow`)
- Parse `A[i:j]` and `A[i:j, k]` — extend `parse_subscript` to consume `:` and produce `Slice` node
- Parse `A.method(args)` postfix — extend `parse_postfix` to consume `.Ident(...)` and produce `MethodCall`

**AST** (`blocks/math/ast.rs`):
- Add `MatMul(Box<MathExpr>, Box<MathExpr>)` variant
- Add `Slice { base: Box<MathExpr>, ranges: Vec<SliceRange> }` where `SliceRange = { start: Option<MathExpr>, end: Option<MathExpr> }`
- Add `MethodCall { receiver: Box<MathExpr>, method: String, args: Vec<MathExpr> }` — or normalise `.T` at parse time to `App("transpose", [receiver])`

**Eval** (`blocks/math/eval/mod.rs`, `tensor_functions.rs`):
- `MatMul` arm → calls `Tensor::matmul`
- `Slice` arm → new `tensor_slice(tensor, ranges)` function in `tensor/indexing.rs`
- `MethodCall` arm → dispatch to same function table as `App` with receiver as first arg
- `App("inv", [A])` → new `eval_inv` in `tensor_functions.rs`; FFI to LAPACK `dgetrf`+`dgetri` or cuSOLVER `cusolverDnDgetrf`
- `App("solve", [A, b])` → new `eval_solve`; FFI to LAPACK `dgesv` or cuSOLVER `cusolverDnDgesv`
- `App("sum", [A, axis])` / `App("mean", [A, axis])` → extend existing `eval_sum_tensor` to accept optional axis integer

**Backend hook for type-directed CUDA dispatch (runtime probe):**
- In `eval_function` for `MatMul`/`inv`/`solve`: check if `MathBackend::CUDA.is_available()` and tensor size exceeds a threshold, then dispatch to `cuda_eval` path
- No change to `auto_select.rs` needed for this; extend `BackendCapability` to flag BLAS-eligible ops

**Rendering** (`blocks/math/rendering/`):
- `MatMul` renders as `A \cdot B` in LaTeX, `A @ B` in Unicode text
- `Slice` renders as `A[i:j,k]` in all formats
- `MethodCall` renders as `A.method(args)` or equivalent notation

### 5.3 Risk Assessment

| Layer | Risk | Severity | Notes |
|-------|------|----------|-------|
| Lexer | `:` token collision with binder `..` range syntax | Low | Math lexer uses `..` as a single token for `Range`; `:` is free |
| Parser | `@` at correct precedence (below `^`, above `+`) | Low | Well-defined; one new arm in `parse_multiplicative` |
| Parser | `A[i:j, k]` multi-axis slice grammar | Medium | Commas inside subscripts must not collide with function-call comma parsing |
| AST | `MethodCall` vs `App` normalisation | Low | Easiest path: normalise `.T` → `App("transpose", [recv])` at parse time; defer full `MethodCall` to Phase 2 |
| Eval | `inv`/`solve` LAPACK FFI | High | These require a new FFI path from inside the math block runtime; no existing LAPACK extern in the Rust seed today |
| Eval | Axis-parameterised reductions | Medium | Changes existing `eval_sum_tensor` dispatch guard (`eval/mod.rs:410` dispatches `sum` with 1 tensor arg); adding optional axis changes the dispatch condition |
| Backend | Runtime-probe type-directed CUDA dispatch | Medium | Depends on cuSOLVER FFI landing (sibling agent scope); the hook slot exists but FFI is new |
| Architecture | Compile-time type-directed dispatch | Very High | Requires rebuilding `math{}` as HIR-level syntax; not recommended for Phase 1; flag as deferred |
| Df | Forcing DataFrame into `math{}` | Critical — avoid | Would require rebuilding `MathExpr` from scratch; no benefit; use plain Simple class API |

**Biggest compiler-side risk:** The runtime-interpreter architecture of `math{}` fundamentally cannot perform compile-time type-directed lowering. If the architecture decision (Phase 3) determines that `A @ B` must emit a cuBLAS call at codegen time based on the static type `NDArray<Float64>`, the current `math{}` block cannot satisfy this without an HIR-level rewrite. This should be the first explicit question resolved in Phase 3 before any parser work begins.

---

## 6. Open Questions for Phase 3

| ID | Question | Blocks |
|----|----------|--------|
| OQ-1 | Is "lower into CUDA backend" runtime dispatch or compile-time HIR emission? | Entire extension plan |
| OQ-2 | Should `@` and slice syntax live in main Simple grammar (HIR-level) as well as inside `math{}`? If so, the parser work should happen at the language level, not just inside the block | Naming harmony |
| OQ-3 | `inv`/`solve` LAPACK FFI — can they use the same `rt_*` extern pattern as the existing runtime, or do they need a new vendored LAPACK layer? | Eval + backend |
| OQ-4 | Axis parameter convention: `sum(A, axis=0)` (keyword arg — not currently supported in math parser) vs `sum(A, 0)` (positional) vs `sum_axis(A, 0)` (separate function)? | API naming harmony |
| OQ-5 | `linalg{}`/`array{}` keyword aliases: useful for scoping user intent or unnecessary complexity given shared semantics? | User-visible API |
