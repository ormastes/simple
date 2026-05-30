# What Cannot Be Expressed in m{} Blocks (Even After Full Implementation)

This document lists fundamental limitations of the `m{}` math block system that are **by design** and won't change even with full feature completion.

---

## ❌ **1. Multi-Statement Imperative Logic**

### Cannot Express:

**Loops with side effects:**
```simple
# ❌ CANNOT DO THIS in m{}:
m{
    result = 0
    for i in 1..10:
        result = result + i^2
    result
}
```

**Why:** Math blocks are **pure expressions**, not imperative programs.

**Workaround:**
```simple
# ✅ Use summation instead:
val result = m{ sum(i, 1..10) i^2 }

# ✅ Or use regular Simple code:
var result = 0
for i in 1..10:
    result = result + i ** 2
```

---

## ❌ **2. Conditional Logic / Piecewise Functions**

### Cannot Express:

**LaTeX piecewise:**
```latex
f(x) = \begin{cases}
  x^2 & \text{if } x \geq 0 \\
  -x^2 & \text{if } x < 0
\end{cases}
```

**Simple attempt:**
```simple
# ❌ CANNOT DO (no cases/match in m{}):
m{
    f(x) = cases(
        x >= 0: x^2,
        x < 0: -x^2
    )
}
```

**Why:** No `if`/`match` inside math expressions.

**Workaround:**
```simple
# ✅ Use regular function:
fn f(x):
    if x >= 0:
        x ** 2
    else:
        -x ** 2

# ✅ Or use max/min tricks for simple cases:
val abs_squared = m{ max(x, -x)^2 }
```

---

## ❌ **3. LaTeX Document Structure**

### Cannot Express:

**Environments:**
```latex
\begin{align}
  x + y &= 5 \\
  2x - y &= 1
\end{align}
```

**Matrices with LaTeX syntax:**
```latex
\begin{bmatrix}
  1 & 2 & 3 \\
  4 & 5 & 6
\end{bmatrix}
```

**Theorem environments:**
```latex
\begin{theorem}
  For all $n > 0$, $n! > 2^n$.
\end{theorem}
```

**Why:** `m{}` is for **expressions**, not LaTeX document markup.

**Workaround:**
```simple
# ✅ Use tensor literals for matrices:
val matrix = [[1, 2, 3], [4, 5, 6]]

# ✅ Use md{} block for documents:
val doc = md{
    ## Theorem

    For all n > 0, we have n! > 2^n.

    The matrix is ${matrix}.
}
```

---

## ❌ **4. Text Labels and Annotations**

### Cannot Express:

**Text in formulas:**
```latex
\text{Attention}(Q, K, V) = \text{softmax}\left(\frac{QK^T}{\sqrt{d_k}}\right)V
```

**Underbrace/overbrace:**
```latex
\underbrace{x + x + \cdots + x}_{n \text{ times}} = nx
```

**Why:** `\text{}` is LaTeX-specific typesetting, not computation.

**Workaround:**
```simple
# ✅ Use variable names:
val attention = m{ softmax(Q @ K' / sqrt(d_k)) @ V }

# ✅ Use comments:
val sum_n_times = m{ n * x }  # x repeated n times
```

---

## ❌ **5. Symbolic Manipulation**

### Cannot Express:

**Simplification:**
```simple
# ❌ CANNOT DO:
m{ simplify((x + 1)^2) }  # Would need to return: x^2 + 2x + 1
```

**Factoring:**
```simple
# ❌ CANNOT DO:
m{ factor(x^2 - 1) }  # Would need to return: (x-1)(x+1)
```

**Algebraic solving:**
```simple
# ❌ CANNOT DO:
m{ solve(x^2 - 4 = 0, x) }  # Would need to return: x = ±2
```

**Why:** No computer algebra system (CAS) in Simple.

**Workaround:**
```simple
# ✅ Use external tools (SymPy, Mathematica, Sage):
# In Python with SymPy:
from sympy import symbols, solve, factor
x = symbols('x')
solutions = solve(x**2 - 4, x)  # [-2, 2]

# Then import results into Simple
val solutions = [-2, 2]
```

---

## ❌ **6. Limits**

### Cannot Express:

**Limit notation:**
```latex
\lim_{x \to 0} \frac{\sin x}{x} = 1
```

**L'Hôpital's rule:**
```latex
\lim_{x \to 0} \frac{e^x - 1}{x} = \lim_{x \to 0} \frac{e^x}{1} = 1
```

**Why:** No symbolic limit computation.

**Workaround:**
```simple
# ✅ Numerical approximation:
fn limit_approx(f, x0, epsilon):
    f(x0 + epsilon)

val result = limit_approx(\x: sin(x) / x, 0.0, 0.0001)
# ≈ 0.9999...

# ✅ Or hardcode known limits:
val sinc_limit = 1.0  # Known: lim(sin(x)/x) = 1 as x→0
```

---

## ❌ **7. Multi-Dimensional Indexing (Complex)**

### Cannot Express:

**Einstein notation:**
```latex
C_{ij} = \sum_k A_{ik} B_{kj}
```

**Tensor contractions:**
```latex
\text{tr}(AB) = \sum_i \sum_j A_{ij} B_{ji}
```

**Why:** No Einstein summation convention in `m{}`.

**Workaround:**
```simple
# ✅ Use explicit summations:
val C_ij = m{ sum(k, 1..n) A[i,k] * B[k,j] }

# ✅ Use tensor library:
import std.torch
val C = torch.einsum("ik,kj->ij", A, B)
```

---

## ❌ **8. Stochastic/Random Operations**

### Cannot Express:

**Random sampling:**
```simple
# ❌ CANNOT DO (not deterministic):
m{ X ~ N(0, 1) }  # Sample from normal distribution
m{ E[X] where X ~ Bernoulli(p) }  # Expectation notation
```

**Probability notation:**
```latex
P(X = k) = \binom{n}{k} p^k (1-p)^{n-k}
```

**Why:** Math blocks are **deterministic** (same input → same output).

**Workaround:**
```simple
# ✅ Use explicit probability functions:
fn binomial_pmf(n, k, p):
    binomial(n, k) * p ** k * (1 - p) ** (n - k)

# ✅ Or use std.random:
import std.random
val sample = random.normal(0.0, 1.0)
```

---

## ❌ **9. Partial Derivatives (Symbolic)**

### Cannot Express:

**Partial derivative operator:**
```latex
\frac{\partial f}{\partial x} = 2x + y
```

**Gradient operator:**
```latex
\nabla f = \left(\frac{\partial f}{\partial x}, \frac{\partial f}{\partial y}\right)
```

**Jacobian matrix:**
```latex
J = \begin{bmatrix}
  \frac{\partial f_1}{\partial x_1} & \frac{\partial f_1}{\partial x_2} \\
  \frac{\partial f_2}{\partial x_1} & \frac{\partial f_2}{\partial x_2}
\end{bmatrix}
```

**Why:** No symbolic differentiation engine.

**Workaround:**
```simple
# ✅ Use autograd (for neural networks):
loss{
    y = f(x)
    # Gradients computed automatically via backward pass
}

# ✅ Use manual derivatives:
val df_dx = m{ 2*x + y }  # If f = x^2 + x*y

# ✅ Use numerical gradients:
fn grad(f, x, epsilon):
    [(f(x + e) - f(x - e)) / (2 * epsilon) for e in epsilon_vector]
```

---

## ❌ **10. Non-Closed Form Expressions**

### Cannot Express:

**Special functions without implementations:**
```simple
# ❌ These may not exist:
m{ Γ(x) }       # Gamma function
m{ ζ(s) }       # Riemann zeta function
m{ Ei(x) }      # Exponential integral
m{ erf(x) }     # Error function (may be added)
m{ BesselJ(n, x) }  # Bessel function
```

**Why:** Limited special function library.

**Workaround:**
```simple
# ✅ Check if function exists, use approximation:
fn gamma_approx(x):
    # Stirling's approximation
    sqrt(2 * pi / x) * (x / e) ** x

# ✅ Or use external library:
import scipy.special
val gamma_val = scipy.special.gamma(5.5)
```

---

## ❌ **11. Recurrence Relations**

### Cannot Express:

**Fibonacci:**
```simple
# ❌ CANNOT DO:
m{
    F(n) = F(n-1) + F(n-2)
    F(0) = 0, F(1) = 1
}
```

**Recursive definitions:**
```simple
# ❌ CANNOT DO:
m{ ackermann(m, n) = if m=0 then n+1 else ... }
```

**Why:** No recursion in math expressions.

**Workaround:**
```simple
# ✅ Use regular function:
fn fibonacci(n):
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)

# ✅ Or use closed form (if exists):
val fib_n = m{
    phi = (1 + sqrt(5)) / 2
    (phi^n - (-phi)^(-n)) / sqrt(5)
}
```

---

## ❌ **12. Matrix Operations (Some)**

### Cannot Express:

**Matrix inverse (symbolic):**
```simple
# ❌ CANNOT DO:
m{ inv([[a, b], [c, d]]) }  # Would need formula with determinant
```

**Eigenvalues (symbolic):**
```simple
# ❌ CANNOT DO:
m{ eigenvalues(A) }  # Would need characteristic polynomial roots
```

**SVD decomposition:**
```simple
# ❌ CANNOT DO:
m{ U, S, V = svd(A) }
```

**Why:** These require iterative algorithms, not closed forms.

**Workaround:**
```simple
# ✅ Use tensor library for numerical computation:
import std.torch
val inv_A = A.inverse()
val eigenvals = A.eig()[0]
val U, S, V = A.svd()
```

---

## ❌ **13. Custom Operators**

### Cannot Express:

**Custom infix operators:**
```simple
# ❌ CANNOT DO:
m{ a ⊗ b }  # Custom tensor product operator
m{ a ⊕ b }  # Custom addition variant
```

**Why:** Fixed set of operators in math grammar.

**Workaround:**
```simple
# ✅ Use function notation:
val tensor_product = m{ kronecker(a, b) }
val custom_add = m{ special_add(a, b) }
```

---

## ❌ **14. Type-Level Computations**

### Cannot Express:

**Type constraints in formulas:**
```simple
# ❌ CANNOT DO:
m{
    sum(i: i32, 1..n: i32) (i: i32)
}
```

**Dependent types:**
```simple
# ❌ CANNOT DO:
m{
    vector: Vec<n>  # Vector of length n (type-level)
}
```

**Why:** Math expressions are value-level, not type-level.

**Workaround:**
```simple
# ✅ Use dimension checking outside m{}:
import std.torch
val result: Tensor<[batch, 10]> = model(input)
```

---

## ❌ **15. Side Effects / IO**

### Cannot Express:

**Printing during evaluation:**
```simple
# ❌ CANNOT DO:
m{
    x = 5
    print "Debug: x = {x}"
    x^2
}
```

**File operations:**
```simple
# ❌ CANNOT DO:
m{ read_data_from_file("data.csv") }
```

**Why:** Math blocks are **pure** (no side effects).

**Workaround:**
```simple
# ✅ Do IO outside, then compute:
val data = read_csv("data.csv")
val result = m{ sum(i, 1..n) data[i]^2 }
```

---

## 📊 **Summary Table**

| Category | Example | Why Not | Workaround |
|----------|---------|---------|------------|
| **Imperative Logic** | `for` loops | Not expressions | Use `sum()`, `prod()` |
| **Conditionals** | `if`/`cases` | No branching | Regular functions |
| **LaTeX Markup** | `\begin{align}` | Not computation | Use `md{}` |
| **Text Labels** | `\text{...}` | Typesetting only | Comments/variable names |
| **Symbolic CAS** | `simplify()` | No CAS engine | External tools |
| **Limits** | `lim` | No symbolic limits | Numerical approximation |
| **Einstein Notation** | `A_{ij}B_{jk}` | Not supported | Explicit sums or einsum |
| **Stochastic** | `X ~ N(μ,σ)` | Not deterministic | `std.random` |
| **Partial Derivatives** | `∂f/∂x` | No symbolic diff | Autograd or manual |
| **Special Functions** | `Γ(x)`, `ζ(s)` | Limited library | Approximations |
| **Recursion** | `F(n)=F(n-1)+F(n-2)` | No recursion | Regular functions |
| **Matrix Inverse** | `inv(A)` symbolic | Needs algorithms | Numerical (torch) |
| **Custom Operators** | `a ⊗ b` | Fixed grammar | Function notation |
| **Type-Level** | Dependent types | Value-level only | External type system |
| **Side Effects** | `print`, `read` | Pure functions | Do outside `m{}` |

---

## 🎯 **Design Philosophy**

The `m{}` block is designed for:
- ✅ **Pure mathematical expressions**
- ✅ **Deterministic computations**
- ✅ **Numerical evaluation**
- ✅ **LaTeX export** (for papers)

It is **NOT** designed for:
- ❌ Computer algebra systems (use SymPy, Mathematica)
- ❌ Imperative programming (use regular Simple)
- ❌ Document typesetting (use LaTeX directly)
- ❌ Symbolic manipulation (use CAS tools)

---

## 💡 **When to Use What**

### Use `m{}` for:
- Mathematical formulas (e.g., `x^2 + 1`)
- Summations/products (e.g., `sum(i, 1..n) i^2`)
- Numerical integration (e.g., `int(x, 0..1) x^2`)
- LaTeX rendering of expressions
- Deep learning loss functions
- Clean mathematical notation

### Use Regular Simple for:
- Control flow (`if`, `for`, `while`)
- Functions with side effects
- File I/O, printing, debugging
- Recursion
- Complex algorithms

### Use Tensor Library for:
- Matrix operations (inverse, eigenvalues, SVD)
- Autograd (neural network gradients)
- Broadcasting and vectorization
- GPU acceleration

### Use External Tools for:
- Symbolic integration (SymPy)
- Symbolic differentiation (SymPy, Mathematica)
- Computer algebra (Sage, Maxima)
- Special functions (SciPy)
- Theorem proving (Lean, Coq)

---

## ✅ **What IS Fully Supported**

To contrast, here's what **DOES** work perfectly:

1. ✅ All arithmetic: `+`, `-`, `*`, `/`, `^`, `%`
2. ✅ All functions: `sqrt`, `exp`, `log`, `sin`, `cos`, `tanh`, etc.
3. ✅ Summation: `sum(i, a..b) expr`
4. ✅ Product: `prod(i, a..b) expr`
5. ✅ Numerical integration: `int(x, a..b) expr`
6. ✅ Matrix multiply: `@` (with tensors)
7. ✅ Broadcasting: `.+`, `.-`, `.*`, `./`, `.^`
8. ✅ Greek letters: `pi`, `alpha`, `beta`, etc.
9. ✅ Implicit multiplication: `2x`, `2(x+1)`
10. ✅ LaTeX rendering: `to_latex()` (Rust API)
11. ✅ Nested expressions: unlimited depth
12. ✅ Subscripts: `x[i]`
13. ✅ Constants: `pi`, `e`, `tau`
14. ✅ Power operator: `^` (m{} only)
15. ✅ Transpose: `A'` (m{} only)

---

## 🎓 **Conclusion**

**The `m{}` block covers 95%+ of deep learning and numerical mathematics.**

The remaining 5% (symbolic manipulation, CAS features, complex control flow) are **intentionally** left to:
- Regular Simple code
- External specialized tools
- Domain-specific libraries

This is a **feature, not a bug** - it keeps the math block focused, fast, and predictable.
