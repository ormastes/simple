Simple Math — Math Operations and Functions (PyTorch-complete surface)

With SDN grid/tensor literals (LL(1)-friendly, one-pass)

Simple math is a math-first tensor extension for Simple language whose semantics default to PyTorch (operators, broadcasting, batched matmul, etc.). Anything not covered by surface syntax is reachable via torch.*.

This revision adds SDN-style grid and tensor blocks that can be used as literals (compile-time constants) and/or as doc-friendly structured data. The blocks are designed to be one-pass parseable with an LL(1) + INDENT/DEDENT lexer model (Python-style), and also work well with Tree-sitter even though Tree-sitter uses GLR under the hood.


---

1) Lexical model and LL(1) constraints

1.1 Indentation tokens

The lexer must emit:

NEWLINE

INDENT / DEDENT (like Python)


All SDN blocks and Simple math constructs rely on indentation for deterministic block structure.

1.2 Reserved keywords for determinism

Reserve these as statement-leading keywords (they never appear as identifiers):

grid, tensor, slice, flat, default


This makes top-level FIRST sets disjoint and keeps the grammar LL(1).

1.3 Pipe rows are SDN-only

A line beginning with | is legal only inside a grid/tensor SDN block. This prevents conflicts with other constructs and keeps parsing single-path.


---

2) Simple math core data model

A Simple math value is a Tensor with:

shape, dtype, optional device (CPU/GPU)

PyTorch/NumPy broadcasting semantics for elementwise ops



---

3) Literals and constructors

3.1 Backend constructors (escape-hatch standard)

x = torch.zeros([2,3], dtype: f32, device: "cuda")
y = torch.randn([2,3])
i = torch.eye(4)


---

4) Indexing and slicing

x[i]
x[i, j]
x[:, 0:10]
x[mask]
x[idx]


---

5) Operators (PyTorch semantics)

5.1 Elementwise arithmetic (broadcasting)

x + y, x - y, x * y, x / y, x ** y
-x

Broadcasting follows PyTorch’s documented broadcasting rules. 

5.2 Matmul

A @ B

@ maps to torch.matmul semantics, including batched matmul when N > 2. 

5.3 Comparisons / boolean ops

x == y, x != y, x < y, x <= y, x > y, x >= y
x & y, x | y, x ^ y
~x


---

6) Shape and dimension transforms

x.shape
x.reshape([a,b,c])
x.permute([2,0,1])
x.transpose(d0, d1)
x.t              # 2D transpose shorthand


---

7) Reductions: min/max, argmin/argmax, sum/mean

7.1 Global reductions

x.sum()
x.mean()
x.prod()
x.max()
x.min()

7.2 Dim reductions (values + indices)

vals, idx = x.max(dim: 1, keepdim: true)
vals, idx = x.min(dim: 1, keepdim: false)

PyTorch returns (values, indices) for min/max when reducing along dim. 

7.3 Indices only

idx = x.argmax(dim: 1)
idx = x.argmin(dim: 1)


---

8) Elementwise math functions (representative set)

x.abs()
x.sqrt()
x.exp()
x.log()
x.sin()
x.cos()
x.tanh()
x.floor()
x.ceil()
x.round()

(Everything else is available via torch.*.)


---

9) Clamp and conditional selection

9.1 Clamp

y = x.clamp(min: 0, max: 1)

9.2 Where

z = cond.where(a, b)

where follows broadcastability requirements (PyTorch/NumPy style). 


---

10) Concatenation and stacking (Ruby-way surface)

10.1 Concat along an existing dim

y = x.concat(w, dim: 0)   # torch.cat
y = x.vcat(w)             # convention: dim: 0
y = x.hcat(w)             # convention: dim: -1 (2D-friendly)

torch.cat requires same shape except in the concatenating dimension. 

10.2 Stack along a new dim

y = x.stack(w, dim: 0)    # torch.stack


---

11) One-hot encoding

labels = [0 2 1 2]
oh = labels.one_hot(num_classes: 4)

Matches torch.nn.functional.one_hot: input shape (*), output shape (*, num_classes). 


---

12) Linear algebra (common essentials)

d  = A.det
Ai = A.inv
x  = A.solve(b)

Suggested lowering:

A.det → torch.linalg.det(A)

A.inv → torch.linalg.inv(A)

A.solve(b) → torch.linalg.solve(A, b)



---

13) FFT (frequency-domain ops)

13.1 Core FFTs

X  = x.fft(n: ?, dim: ?, norm: ?)
x2 = X.ifft(n: ?, dim: ?, norm: ?)

Xr = x.rfft(n: ?, dim: ?, norm: ?)
x0 = Xr.irfft(n: ?, dim: ?, norm: ?)

F  = x.fftn(s: ?, dim: ?, norm: ?)
xN = F.ifftn(s: ?, dim: ?, norm: ?)

rfft returns the one-sided spectrum because real-input FFTs are Hermitian-symmetric. 

13.2 fftshift / ifftshift

Xs = X.fftshift(dim: ?)
Xu = Xs.ifftshift(dim: ?)

fftshift reorders frequencies from negative→positive with the DC term centered. 


---

14) SDN grid and tensor literals (one-pass, LL(1))

These blocks may appear:

as statements defining named constants, or

as primary expressions (right-hand side of =).

See also: `doc/spec/sdn.md` for full SDN specification.


14.1 grid (2D matrix)

Statement form

grid A:
    | r\c | 0 | 1 |
    | 0   | 3 | 1 |
    | 1   | 1 | 2 |

Expression form

A = grid:
    | r\c | 0 | 1 |
    | 0   | 3 | 1 |
    | 1   | 1 | 2 |

Rules (LL(1)-friendly)

After grid and :, the next non-empty line must start with | (header row).

All grid rows are | cell | cell | ... | with consistent column count.


Ruby interoperability note (doc-level): elementwise product is "Hadamard"; Ruby's stdlib Matrix exposes hadamard_product/entrywise_product.

14.2 tensor (N-D with explicit render mode)

Header

tensor K: Float [d=2, h=3, w=4]
    ...

After the header, exactly one of:

slice ...: (human-readable)

flat: (diff/sparse-friendly)


Slice mode (recommended for docs)

tensor K: Float [d=2, h=3, w=4]
    slice d=0:
        | h\w | 0    | 1    | 2    | 3    |
        | 0   | 0.01 | 0.02 | 0.03 | 0.04 |
        | 1   | 0.05 | 0.06 | 0.07 | 0.08 |
        | 2   | 0.09 | 0.10 | 0.11 | 0.12 |

    slice d=1:
        | h\w | 0    | 1    | 2    | 3    |
        | 0   | 0.13 | 0.14 | 0.15 | 0.16 |
        | 1   | 0.17 | 0.18 | 0.19 | 0.20 |
        | 2   | 0.21 | 0.22 | 0.23 | 0.24 |

Flat mode (sparse / large tensors)

tensor K: Float [d=2, h=3, w=4]
    default: 0
    flat:
        | d | h | w | value |
        | 0 | 0 | 0 | 0.01  |
        | 0 | 0 | 1 | 0.02  |
        | 1 | 2 | 3 | 0.24  |


---

15) LL(1) grammar sketch (core + SDN blocks)

Assume INDENT/DEDENT tokens are provided by the lexer.

15.1 Top-level statements (FIRST sets are disjoint)

Stmt
  := GridDecl
   | TensorDecl
   | AssignStmt
   | ExprStmt

GridDecl   := "grid" Ident? ":" NEWLINE INDENT GridRows DEDENT
TensorDecl := "tensor" Ident ":" Type DimList NEWLINE INDENT TensorBody DEDENT
AssignStmt := Ident "=" Expr
ExprStmt   := Expr

FIRST(Stmt) = {grid, tensor, IDENT, …}

grid and tensor are unique leaders → no ambiguity (LL(1)).


15.2 Grid rows (pipe-led rows are unambiguous)

GridRows   := GridRow GridRow+
GridRow    := "|" Cell ("|" Cell)+ "|" NEWLINE
Cell       := Scalar | QuotedString | Ident | Empty

15.3 Tensor bodies (mode keyword is decisive)

TensorBody := (SliceBlock+)
            | (DefaultLine? FlatBlock)

SliceBlock := "slice" Ident "=" Int ":" NEWLINE INDENT (SliceBlock | GridRows) DEDENT
FlatBlock  := "flat" ":" NEWLINE INDENT GridRows DEDENT
DefaultLine:= "default" ":" Scalar NEWLINE

FIRST(TensorBody) = {slice, default, flat}

With a 1-token lookahead, the parser selects the correct alternative.



---

16) PyTorch-completeness rule (escape hatch)

If Simple math doesn't define a surface form:

y = torch.op_name(x, ...)
y = x.torch("op_name", ...)

This keeps the language small while retaining access to the full PyTorch API surface.


---

17) PyTorch/CUDA Alignment

Simple Math builds on the existing ML/PyTorch Integration (#1650-#1729, 80 features).

17.1 Already implemented (reuse from PyTorch module)

| Feature | PyTorch Module | Simple Math Surface |
|---------|----------------|---------------------|
| Tensor creation | torch.zeros, ones, rand | grid:, tensor: literals |
| Basic ops | torch.add, sub, mul, div | +, -, *, / operators |
| Matrix multiply | torch.matmul | @ operator |
| Transpose | torch.transpose | .t, .T |
| Reshape | torch.reshape | .reshape([...]) |
| Indexing | tensor[i, j] | x[i, j] |
| Slicing | tensor[:, 0:10] | x[:, 0:10] |
| CUDA support | device="cuda" | grid device="cuda": |
| Autograd | torch.autograd | Automatic |

17.2 New bindings needed for Simple Math

| PyTorch API | Simple Math Surface | Status |
|-------------|---------------------|--------|
| torch.linalg.det | A.det | New FFI |
| torch.linalg.inv | A.inv | New FFI |
| torch.linalg.solve | A.solve(b) | New FFI |
| torch.fft.fft | x.fft(dim:) | New FFI |
| torch.fft.ifft | X.ifft(dim:) | New FFI |
| torch.fft.rfft | x.rfft(dim:) | New FFI |
| torch.fft.irfft | Xr.irfft(dim:) | New FFI |
| torch.fft.fftn | x.fftn(dims:) | New FFI |
| torch.fft.fftshift | X.fftshift(dim:) | New FFI |
| torch.fft.ifftshift | Xs.ifftshift(dim:) | New FFI |

17.3 CUDA device support

Grid and tensor literals support explicit device:

```simple
# CPU (default)
A = grid:
    | 3 | 1 |
    | 1 | 2 |

# CUDA GPU
A_gpu = grid device="cuda":
    | 3 | 1 |
    | 1 | 2 |

# Specific GPU
tensor K: Float [d=2, h=3] device="cuda:1"
    slice d=0:
        | h | 0   | 1   | 2   |
        | 0 | 1.0 | 2.0 | 3.0 |
```

17.4 Integration with existing torch module

```simple
import ml.torch as torch
import ml.math  # Simple Math surface

# SDN grid literal → torch.tensor
A = grid:
    | 3 | 1 |
    | 1 | 2 |

# Equivalent to:
A_manual = torch.tensor([[3, 1], [1, 2]])

# Both support the same operations
result = A @ A.t      # Simple Math style
result = torch.matmul(A_manual, A_manual.T)  # PyTorch style

# Escape hatch for unlisted ops
eigenvalues = A.torch("linalg.eigvalsh")
```

---

18) Implementation Plan

See: `doc/plans/simple_math_implementation.md`

Feature range: #1910-#1969 (60 features)

| Phase | Features | Description |
|-------|----------|-------------|
| 1 | #1910-#1919 | Parser extensions (grid, tensor keywords) |
| 2 | #1920-#1929 | AST/HIR integration |
| 3 | #1930-#1939 | Operator extensions (@, broadcasting) |
| 4 | #1940-#1949 | Math methods (reductions, elementwise) |
| 5 | #1950-#1959 | Linear algebra & FFT |
| 6 | #1960-#1969 | Integration tests & docs |
