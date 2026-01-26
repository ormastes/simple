# Math Language Comparison: Fortran/R/MATLAB/Julia/NumPy vs Simple

**Date:** 2026-01-26
**Status:** Research Complete
**Related:** `doc/design/math_block_design.md`, `doc/research/math.md`

## 1. What Math-Oriented Languages Get Right (Distilled)

### 1.1 Core Strengths (Common Pattern)

Across Fortran, MATLAB, Julia, R:

| Capability | Why It Matters |
|------------|----------------|
| First-class multidimensional arrays | Math is expressed over tensors, not scalars |
| Whole-array expressions | Matches mathematical notation |
| Implicit vectorization | Avoids boilerplate loops |
| Reductions (sum, mean, norm, etc.) | Core to math & statistics |
| Broadcasting rules | Shape-aware operations |
| Domain blocks / environments | Math code is visually and semantically distinct |

**Mental model:** "I am writing math, not algorithms."

---

## 2. Where Simple Already Aligns Well

Based on existing design goals and implemented features:

| Feature | Status | Notes |
|---------|--------|-------|
| `m{}` math blocks | **Implemented** | Excellent foundation |
| `^` power in m{} | **Implemented** | Context-aware lexing |
| `xor` keyword | **Implemented** | Bitwise XOR |
| `@` matmul operator | **Implemented** | Matrix multiplication |
| Dotted operators | **Implemented** | `.+`, `.-`, `.*`, `./`, `.^` |
| SDN table literals | Existing | Close to R data.frame / Julia NamedArrays |
| Explicit GPU/SIMD intent | Planned | `@simd`, CUDA plans |
| Static typing | Existing | Stronger than R/MATLAB |
| Custom blocks extensibility | Existing | Very powerful |

**Simple is structurally closer to Julia than to Python.**

---

## 3. Gaps vs Math-Oriented Languages (Precise)

### 3.1 Array Semantics Under-Specified

Currently missing or implicit:
- Rank / shape semantics
- Broadcasting rules (formal specification)
- Reduction operators as syntax (not just functions)
- Axis-aware operations

Without these, math code degrades into procedural code.

### 3.2 m{} Expressive but Not Math-Dense Enough

Compared to Julia / MATLAB:
- No implicit multiplication (`2x`, `Ax`)
- No concise reduction syntax
- No symbolic-like readability (even numeric)

### 3.3 Statistics is Library-Level, Not Language-Level

R succeeds because:
- `mean`, `sd`, `lm`, etc. feel native
- Formula syntax (`y ~ x1 + x2`) is declarative

Simple currently treats statistics as just another library.

---

## 4. Grammar Improvement Proposals (Concrete)

### 4.1 First-Class Tensor Type (Minimal, LL(1)-Safe)

```simple
type Tensor<T, N>     # N = rank
type Matrix<T> = Tensor<T, 2>
type Vector<T> = Tensor<T, 1>
```

Usage:
```simple
val A: Matrix<f64>
val x: Vector<f64>
val y = A @ x
```

**Why:**
- Matches Fortran/MATLAB mental model
- Enables compile-time shape checking
- Enables GPU lowering automatically

### 4.2 Broadcasting as Syntax, Not Convention

**Status: IMPLEMENTED**

Borrow from Julia, simplified:
```simple
y = x .+ 1
z = A .* B
```

Grammar rule:
```
expr ::= expr '.' op expr
```

Semantics:
- `.` operator means element-wise
- Shape inference at compile time where possible

**This is the single most important math usability upgrade.**

### 4.3 Reduction Operators as Postfix Methods

Instead of:
```simple
sum(x)
mean(x)
```

Allow:
```simple
x.sum
x.mean
x.std
x.norm
```

With axis:
```simple
A.sum(axis: 0)
A.mean(axis: 1)
```

This mirrors:
- MATLAB: `sum(A,1)`
- Julia: `sum(A, dims=1)`
- NumPy: `A.sum(axis=0)`

But cleaner.

### 4.4 m{} Block Upgrade: Implicit Math Rules

**Status: Phase 2 (Planned)**

Inside `m{}` only:

**1. Implicit multiplication**
```simple
m{
    y = 2x + 3
    z = Ax + b
}
```

Parser rule:
- `number ident` → multiplication
- `ident ident` → multiplication (only in m{})

**This is huge for readability and safe because scope-limited.**

**2. Math-native operators**

Inside m{}:
```
^    # power (IMPLEMENTED)
@    # matrix multiply (IMPLEMENTED)
'    # transpose (PLANNED)
```

Example:
```simple
m{
    y = (A' A)^-1 A' b
}
```

This is MATLAB/Julia-level clarity.

### 4.5 Statistical Formula Block (stat{})

**Status: Phase 3 (Proposed)**

Inspired by R, but typed and static.

```simple
stat{
    model = y ~ x1 + x2 + log(x3)
    fit model using linear
}
```

Desugars to:
- Design matrix generation
- Typed regression call
- Optional GPU backend

**This should not be a library API; it should be a language block.**

### 4.6 SDN Table → DataFrame Unification

You already have SDN tables.

Upgrade semantics:
```simple
val t = table{
    age: [23, 31, 45]
    income: [3000, 4200, 5100]
}
```

Enable:
```simple
t.age.mean
t.where(age > 30).income.std
```

This makes Simple competitive with:
- R data.frame
- pandas
- Julia DataFrames

### 4.7 Axis-Aware Slicing Syntax

```simple
A[:, 0]
A[1..3, :]
A[.., i]
```

**This must be syntax, not function calls.**

---

## 5. GPU & SIMD Tie-In (Where Simple Can Surpass Others)

Unlike MATLAB / R:
```simple
@simd
@cuda
m{
    y = A @ x + b
}
```

Compiler guarantees:
- Shape-safe lowering
- Kernel fusion
- No silent scalar fallbacks (a huge Python problem)

**This is where Simple can be strictly better than Python/Julia.**

---

## 6. Implementation Priority

### Phase 1 (Highest ROI) - **COMPLETE**

| Feature | Status |
|---------|--------|
| `xor` keyword | **Done** |
| `@` matmul operator | **Done** |
| Dotted operators (`.+`, `.-`, `.*`, `./`, `.^`) | **Done** |
| `m{}` blocks with `^` power | **Done** |

### Phase 2 (Next Priority)

| Feature | Status |
|---------|--------|
| Tensor / Matrix / Vector types | Planned |
| Postfix reductions (`x.sum`) | Planned |
| Axis-aware slicing | Planned |
| Transpose `'` (m{} only) | Planned |
| Transpose `.T` property | Planned |
| `m{}` implicit multiplication | Planned |

### Phase 3 (Future)

| Feature | Status |
|---------|--------|
| `stat{}` formula block | Proposed |
| SDN → DataFrame semantics | Proposed |
| GPU-first lowering guarantees | Proposed |

---

## 7. Final Positioning Statement for Simple

| Language | Positioning |
|----------|-------------|
| Fortran | Fast numeric kernels |
| R | Statistics language |
| MATLAB | Engineering calculator |
| Julia | High-performance math language |
| **Simple** | **Statically typed, GPU-first, math-native systems language** |

---

## 8. Next Steps

1. **Phase 2a:** Add Tensor/Matrix/Vector type aliases
2. **Phase 2b:** Add postfix reduction methods (`.sum`, `.mean`, etc.)
3. **Phase 2c:** Add axis-aware slicing syntax
4. **Phase 2d:** Add transpose operators (`'` in m{}, `.T` outside)
5. **Phase 2e:** Add implicit multiplication in m{}

---

## References

- `doc/design/math_block_design.md` - Implementation design
- `doc/research/math.md` - PyTorch integration spec
- `simple/std_lib/test/features/math_language_spec.spl` - Test specification
