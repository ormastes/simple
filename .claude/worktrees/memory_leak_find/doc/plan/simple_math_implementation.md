# Simple Math Implementation Plan

**Status:** Planned
**Feature Range:** #1910-#1969
**Dependencies:** ML/PyTorch (#1650-#1729), SDN (#601-605), Parser

---

## Overview

Simple Math is a math-first tensor extension for Simple language that provides:
1. **SDN grid/tensor literals** - Human-readable matrix and N-D tensor syntax
2. **PyTorch-compatible operators** - Broadcasting, matmul, elementwise ops
3. **Unified math API** - Consistent surface syntax backed by torch.*

This builds on the existing 80-feature PyTorch integration (#1650-#1729) by adding math-friendly syntax sugar.

---

## Architecture

```
Simple Math Syntax Layer
         │
         ▼
┌─────────────────────────────────────────┐
│  Parser Extensions                       │
│  - grid keyword parsing                  │
│  - tensor keyword parsing                │
│  - @ operator (matmul)                   │
│  - Broadcasting type checking            │
└─────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────┐
│  SDN Integration                         │
│  - Grid literal → torch.tensor()         │
│  - Tensor literal → torch.tensor()       │
│  - Slice/flat mode parsing               │
└─────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────┐
│  Existing PyTorch Runtime (80 features)  │
│  - torch.* FFI bindings                  │
│  - CUDA device support                   │
│  - Autograd, nn modules                  │
└─────────────────────────────────────────┘
```

---

## Feature Breakdown

### Phase 1: Parser Extensions (#1910-#1919) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1910 | `grid` keyword lexer | 2 | R | Add `grid` as reserved keyword |
| #1911 | `tensor` keyword lexer | 2 | R | Add `tensor` as reserved keyword |
| #1912 | `slice` keyword lexer | 1 | R | Add `slice` as reserved keyword |
| #1913 | `flat` keyword lexer | 1 | R | Add `flat` as reserved keyword |
| #1914 | `default` keyword lexer | 1 | R | Add `default` as reserved keyword |
| #1915 | Grid literal parsing | 3 | R | Parse `grid A: \| ... \|` syntax |
| #1916 | Tensor header parsing | 3 | R | Parse `tensor K: Float [d=2, h=3]` |
| #1917 | Slice block parsing | 3 | R | Parse `slice d=0:` blocks |
| #1918 | Flat block parsing | 2 | R | Parse `flat:` blocks with default |
| #1919 | Pipe-row parsing | 2 | R | Parse `\| cell \| cell \|` rows |

### Phase 2: AST/HIR Integration (#1920-#1929) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1920 | GridLiteral AST node | 2 | R | AST representation for grid |
| #1921 | TensorLiteral AST node | 3 | R | AST representation for tensor |
| #1922 | Grid → HIR lowering | 3 | R | Lower grid to torch.tensor call |
| #1923 | Tensor → HIR lowering | 4 | R | Lower tensor to torch.tensor call |
| #1924 | Slice mode HIR | 3 | R | Lower slice syntax to indices |
| #1925 | Flat mode HIR | 3 | R | Lower sparse flat data |
| #1926 | Grid expression form | 2 | R | Support `A = grid:` syntax |
| #1927 | Tensor expression form | 2 | R | Support `T = tensor:` syntax |
| #1928 | Header row extraction | 2 | R | Extract column names from grid |
| #1929 | Axis label extraction | 2 | R | Extract `r\c` axis labels |

### Phase 3: Operator Extensions (#1930-#1939) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1930 | `@` matmul operator | 2 | R | Parse `A @ B` → torch.matmul |
| #1931 | Elementwise `*` | 1 | R | Already exists, verify tensor support |
| #1932 | Elementwise `/` | 1 | R | Already exists, verify tensor support |
| #1933 | Elementwise `**` | 2 | R | Power operator for tensors |
| #1934 | Broadcast type checking | 4 | R | Validate PyTorch broadcast rules |
| #1935 | Shape inference | 4 | R | Infer output shapes at compile time |
| #1936 | `.t` transpose shorthand | 2 | S | Method alias for transpose(0,1) |
| #1937 | `.T` property | 2 | S | Property alias for transpose |
| #1938 | Batch matmul | 2 | R | Support N>2 dimensional matmul |
| #1939 | Broadcasting errors | 3 | R | Clear error messages for shape mismatch |

### Phase 4: Math Methods (#1940-#1949) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1940 | Reduction methods | 2 | S | sum, mean, prod, max, min |
| #1941 | Dim reductions | 2 | S | max(dim:), min(dim:), sum(dim:) |
| #1942 | argmax/argmin | 2 | S | Index-returning reductions |
| #1943 | Elementwise math | 2 | S | abs, sqrt, exp, log, sin, cos |
| #1944 | Clamp method | 1 | S | clamp(min:, max:) |
| #1945 | Where method | 2 | S | cond.where(a, b) |
| #1946 | Concat methods | 2 | S | concat, vcat, hcat |
| #1947 | Stack method | 2 | S | stack(dim:) |
| #1948 | One-hot encoding | 2 | S | labels.one_hot(num_classes:) |
| #1949 | Shape methods | 1 | S | shape, reshape, permute, transpose |

### Phase 5: Linear Algebra (#1950-#1959) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1950 | Determinant | 2 | S | A.det → torch.linalg.det |
| #1951 | Inverse | 2 | S | A.inv → torch.linalg.inv |
| #1952 | Solve | 3 | S | A.solve(b) → torch.linalg.solve |
| #1953 | FFT | 3 | S | x.fft(dim:) |
| #1954 | IFFT | 3 | S | X.ifft(dim:) |
| #1955 | RFFT | 3 | S | x.rfft(dim:) for real input |
| #1956 | IRFFT | 3 | S | Xr.irfft(dim:) |
| #1957 | FFTN | 3 | S | Multi-dimensional FFT |
| #1958 | fftshift | 2 | S | Frequency reordering |
| #1959 | ifftshift | 2 | S | Inverse frequency shift |

### Phase 6: Integration & Tests (#1960-#1969) - 10 features

| ID | Feature | Difficulty | Impl | Description |
|----|---------|------------|------|-------------|
| #1960 | Grid literal tests | 2 | S | Test grid parsing and conversion |
| #1961 | Tensor literal tests | 3 | S | Test tensor parsing and conversion |
| #1962 | Matmul operator tests | 2 | S | Test @ operator semantics |
| #1963 | Broadcasting tests | 3 | S | Test broadcast shape validation |
| #1964 | Math method tests | 2 | S | Test reduction and math methods |
| #1965 | Linear algebra tests | 3 | S | Test linalg operations |
| #1966 | FFT tests | 3 | S | Test frequency domain ops |
| #1967 | torch.* escape hatch | 1 | S | Verify x.torch("op", ...) works |
| #1968 | Documentation | 2 | - | Update spec docs |
| #1969 | Example programs | 2 | S | Example .spl files |

---

## PyTorch/CUDA Alignment

### Existing Features to Leverage (from #1650-#1729)

| Existing Feature | Simple Math Usage |
|------------------|-------------------|
| torch.tensor() | Backend for grid/tensor literals |
| torch.matmul() | Backend for @ operator |
| torch.add/sub/mul/div | Already available, extend with broadcast checking |
| CUDA device support | Grid/tensor literals support `device:` parameter |
| Autograd | Grid/tensor values are autograd-compatible |
| torch.linalg.* | Backend for det, inv, solve |
| torch.fft.* | Backend for fft, ifft, rfft, etc. |

### New PyTorch Bindings Needed

| Function | Simple Math Surface |
|----------|---------------------|
| torch.linalg.det | A.det |
| torch.linalg.inv | A.inv |
| torch.linalg.solve | A.solve(b) |
| torch.fft.fft | x.fft(dim:) |
| torch.fft.ifft | X.ifft(dim:) |
| torch.fft.rfft | x.rfft(dim:) |
| torch.fft.irfft | Xr.irfft(dim:) |
| torch.fft.fftn | x.fftn(dims:) |
| torch.fft.fftshift | X.fftshift(dim:) |
| torch.fft.ifftshift | Xs.ifftshift(dim:) |

### CUDA Integration

Grid and tensor literals should support device specification:

```simple
# CPU tensor
A = grid:
    | 3 | 1 |
    | 1 | 2 |

# CUDA tensor
A_cuda = grid device="cuda":
    | 3 | 1 |
    | 1 | 2 |

# Tensor with explicit device
tensor K: Float [d=2, h=3] device="cuda:0"
    slice d=0:
        | h | 0   | 1   | 2   |
        | 0 | 1.0 | 2.0 | 3.0 |
```

---

## Implementation Order

### Sprint 1: Parser Foundation (Week 1)
1. Add reserved keywords (#1910-#1914)
2. Implement grid parsing (#1915, #1919)
3. Add GridLiteral AST node (#1920)

### Sprint 2: Grid Literals (Week 2)
1. Grid → HIR lowering (#1922)
2. Grid expression form (#1926)
3. Header extraction (#1928)
4. Basic tests (#1960)

### Sprint 3: Tensor Literals (Week 3)
1. Tensor header parsing (#1916)
2. Slice/flat parsing (#1917-#1918)
3. TensorLiteral AST (#1921)
4. Tensor → HIR lowering (#1923-#1925)

### Sprint 4: Operators (Week 4)
1. @ matmul operator (#1930)
2. Broadcasting validation (#1934-#1935)
3. Operator tests (#1962-#1963)

### Sprint 5: Math Methods (Week 5)
1. Reduction methods (#1940-#1942)
2. Elementwise math (#1943)
3. Shape methods (#1949)
4. Method tests (#1964)

### Sprint 6: Linear Algebra & FFT (Week 6)
1. Linalg operations (#1950-#1952)
2. FFT operations (#1953-#1959)
3. Tests and docs (#1965-#1969)

---

## Files to Modify

### Parser (src/parser/)
- `src/parser/src/lexer/mod.rs` - Add keywords
- `src/parser/src/statements/mod.rs` - Grid/tensor statements
- `src/parser/src/ast/nodes/definitions.rs` - AST nodes

### Compiler (src/compiler/)
- `src/compiler/src/hir/lower/expr/lowering.rs` - Lower to torch calls
- `src/compiler/src/interpreter_expr.rs` - Interpret grid/tensor

### Runtime (src/runtime/)
- `src/runtime/src/value/torch/` - Add linalg, fft bindings

### Standard Library (simple/std_lib/src/)
- `ml/torch/linalg.spl` - Linear algebra methods
- `ml/torch/fft.spl` - FFT methods
- `ml/math.spl` - Math-first API wrapper

### Tests (simple/std_lib/test/)
- `unit/ml/math/grid_spec.spl`
- `unit/ml/math/tensor_spec.spl`
- `unit/ml/math/operators_spec.spl`
- `unit/ml/math/linalg_spec.spl`
- `unit/ml/math/fft_spec.spl`

---

## Success Criteria

1. **Grid literals work** - `grid A: | 3 | 1 | ...` creates torch tensors
2. **Tensor literals work** - N-D tensors with slice/flat modes
3. **@ operator works** - `A @ B` performs matmul with broadcasting
4. **Math methods work** - sum, mean, det, fft, etc.
5. **CUDA support** - Literals support `device:` parameter
6. **Escape hatch works** - `torch.op_name(...)` for unlisted ops
7. **All tests pass** - 60 features with full test coverage

---

## Related Documents

- [math.md](../research/math.md) - Simple Math specification
- [sdn.md](../spec/sdn.md) - SDN specification (grid/tensor syntax)
- [PYTORCH_FINAL_IMPLEMENTATION_2025-12-28.md](../report/PYTORCH_FINAL_IMPLEMENTATION_2025-12-28.md) - PyTorch status
- [feature_done_20.md](../features/done/feature_done_20.md) - PyTorch features #1650-#1729
