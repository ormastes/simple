# Math Block: Future Research Directions & Comparison with Lean4/CUDA

**Date:** 2026-02-01
**Question:** What features could be added with research? How does Simple compare to Lean4 and CUDA math libraries?

---

## 📊 **Feature Classification**

| Category | Current Status | Could Add? | Research Difficulty | Lean4 | CUDA |
|----------|---------------|------------|---------------------|-------|------|
| **Symbolic Differentiation** | ❌ Not implemented | ✅ **YES** - High priority | Medium | ✅ Has | ❌ No |
| **Symbolic Integration** | ❌ Not implemented | ✅ **YES** - Hard problem | Hard | ✅ Has | ❌ No |
| **Partial Derivatives** | ❌ Not implemented | ✅ **YES** - With symbolic diff | Medium | ✅ Has | ❌ No |
| **Limits** | ❌ Not implemented | ✅ **YES** - Symbolic computation | Hard | ✅ Has | ❌ No |
| **Simplification** | ❌ Not implemented | ✅ **YES** - CAS required | Hard | ✅ Has | ❌ No |
| **Piecewise Functions** | ❌ Not implemented | ✅ **YES** - Syntax addition | Easy | ✅ Has | ⚠️ Conditional |
| **Special Functions** | ⚠️ Partial | ✅ **YES** - Add implementations | Easy-Medium | ✅ Has | ✅ Has |
| **Multi-line/Align** | ❌ Not implemented | ⚠️ **MAYBE** - Design issue | Medium | ❌ No | ❌ No |
| **Text Labels** | ❌ Not implemented | ⚠️ **MAYBE** - Typesetting only | Easy | ❌ No | ❌ No |
| **Imperative Logic** | ❌ By design | ❌ **NO** - Contradicts design | N/A | ⚠️ Different | ❌ No |
| **Side Effects** | ❌ By design | ❌ **NO** - Purity required | N/A | ⚠️ Different | ❌ No |
| **LaTeX Environments** | ❌ By design | ❌ **NO** - Not computation | N/A | ❌ No | ❌ No |

---

## ✅ **HIGH PRIORITY - Should Add (Research Feasible)**

### 1. **Symbolic Differentiation** ✅

**Why it's missing:** No symbolic differentiation engine implemented yet.

**Can we add it?** ✅ **YES** - Well-understood problem

**Research approach:**
```rust
// Implement symbolic differentiation rules
impl MathExpr {
    fn differentiate(&self, var: &str) -> MathExpr {
        match self {
            // Power rule: d/dx(x^n) = n*x^(n-1)
            MathExpr::BinOp { op: Op::Pow, lhs: x, rhs: n } if x.is_var(var) => {
                MathExpr::Mul(n.clone(), MathExpr::Pow(x.clone(), n - 1))
            }

            // Chain rule: d/dx(f(g(x))) = f'(g(x)) * g'(x)
            MathExpr::Call { func, arg } => {
                let f_prime = func.derivative();
                let g_prime = arg.differentiate(var);
                f_prime.compose(arg) * g_prime
            }

            // ... more rules
        }
    }
}
```

**Example usage:**
```simple
# Future syntax:
val derivative = m{ diff(x^2 + sin(x), x) }
# → 2*x + cos(x)

val gradient = m{ grad(x^2 + y^2, [x, y]) }
# → [2*x, 2*y]
```

**Lean4 comparison:**
```lean
-- Lean4 has symbolic differentiation
import Mathlib.Analysis.Calculus.Deriv

def f (x : ℝ) := x^2 + Real.sin x

#check deriv f  -- Computes derivative symbolically
```

**CUDA comparison:** ❌ No symbolic differentiation (numerical only)

**Difficulty:** Medium (2-3 months for basic implementation)

---

### 2. **Special Functions** (erf, gamma, bessel, etc.) ✅

**Why it's missing:** Limited function library.

**Can we add it?** ✅ **YES** - Just need implementations

**Functions to add:**

| Function | Use Case | Lean4 | CUDA | Difficulty |
|----------|----------|-------|------|------------|
| `erf(x)` | Error function (GELU, stats) | ✅ Yes | ✅ Yes (`erff`) | Easy |
| `gamma(x)` | Gamma function (combinatorics) | ✅ Yes | ❌ No | Medium |
| `bessel(n, x)` | Bessel functions (physics) | ✅ Yes | ❌ No | Hard |
| `zeta(s)` | Riemann zeta (number theory) | ✅ Yes | ❌ No | Hard |
| `digamma(x)` | Polygamma functions | ✅ Yes | ❌ No | Medium |
| `beta(a, b)` | Beta function (stats) | ✅ Yes | ❌ No | Easy |
| `elliptic_k(m)` | Elliptic integrals | ✅ Yes | ❌ No | Hard |

**Implementation:**
```rust
// Add to math function library
pub fn erf(x: f64) -> f64 {
    // Taylor series or numerical approximation
    libm::erf(x)  // Use existing C library
}

pub fn gamma(x: f64) -> f64 {
    // Lanczos approximation or Stirling's formula
    libm::tgamma(x)
}
```

**CUDA has:**
- `erff(x)`, `erfcf(x)` - Error functions ✅
- `tgammaf(x)`, `lgammaf(x)` - Gamma functions ✅
- `j0f(x)`, `j1f(x)`, `y0f(x)`, `y1f(x)` - Bessel functions (limited) ⚠️

**Difficulty:** Easy to Medium (1-2 weeks per function)

---

### 3. **Piecewise Functions** ✅

**Why it's missing:** No syntax for conditional expressions in m{}.

**Can we add it?** ✅ **YES** - Add special syntax

**Proposed syntax:**
```simple
# Option 1: cases() function
val f = m{
    cases(
        x >= 0: x^2,
        x < 0: -x^2
    )
}

# Option 2: Ternary-like syntax
val f = m{ if x >= 0 then x^2 else -x^2 }

# Option 3: Pattern matching style
val f = m{
    match x:
        >= 0: x^2
        < 0: -x^2
}
```

**LaTeX rendering:**
```latex
f(x) = \begin{cases}
  x^2 & \text{if } x \geq 0 \\
  -x^2 & \text{if } x < 0
\end{cases}
```

**Lean4 comparison:**
```lean
-- Lean4 has conditional expressions
def f (x : ℝ) : ℝ := if x ≥ 0 then x^2 else -x^2
```

**CUDA comparison:**
```cuda
// CUDA has ternary operator
__device__ float f(float x) {
    return (x >= 0) ? x*x : -x*x;
}
```

**Difficulty:** Easy (1-2 weeks)

---

## ⚠️ **MEDIUM PRIORITY - Possible but Complex**

### 4. **Symbolic Integration** ⚠️

**Why it's missing:** Very hard problem (AI-complete).

**Can we add it?** ✅ **YES** - But extremely difficult

**Challenge:** Integration is much harder than differentiation:
- No general algorithm (unlike differentiation)
- Requires pattern matching and heuristics
- Many integrals have no closed form

**Research approach:**
1. **Risch algorithm** - Complete for elementary functions (very complex)
2. **Table lookup** - Pre-computed integral rules
3. **Pattern matching** - Heuristic-based (like SymPy)

**Example (theoretical):**
```simple
# Future syntax:
val antiderivative = m{ integrate(x^2, x) }
# → x^3/3 + C

val definite = m{ integrate(sin(x), x, 0..pi) }
# → 2 (computed symbolically)
```

**Lean4 comparison:**
```lean
-- Lean4 has symbolic integration (via tactics)
import Mathlib.Analysis.Calculus.Integral

theorem integral_x_squared :
  ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  -- Proof using calculus tactics
  sorry
```

**CUDA comparison:** ❌ No symbolic integration (numerical only)

**Difficulty:** Very Hard (6-12 months research project)

**Recommendation:** Use external tools (SymPy) for now, add later if needed.

---

### 5. **Limits** ⚠️

**Why it's missing:** Requires symbolic computation.

**Can we add it?** ✅ **YES** - Moderate difficulty

**Research approach:**
```rust
impl MathExpr {
    fn limit(&self, var: &str, point: LimitPoint) -> Result<MathExpr, LimitError> {
        match point {
            LimitPoint::Finite(a) => {
                // Try direct substitution
                if let Ok(val) = self.substitute(var, a).simplify() {
                    return Ok(val);
                }

                // Apply L'Hôpital's rule if indeterminate
                if self.is_indeterminate_at(var, a) {
                    let numerator = self.numerator();
                    let denominator = self.denominator();
                    return (numerator.diff(var) / denominator.diff(var)).limit(var, a);
                }
            }
            LimitPoint::Infinity => {
                // Leading term analysis
                self.leading_term(var)
            }
        }
    }
}
```

**Example:**
```simple
# Future syntax:
val limit_result = m{ lim(sin(x)/x, x, 0) }
# → 1

val limit_infinity = m{ lim(1/x, x, inf) }
# → 0
```

**Lean4 comparison:**
```lean
-- Lean4 has limit notation
import Mathlib.Topology.Basic

example : Filter.Tendsto (fun x => Real.sin x / x) (𝓝 0) (𝓝 1) := by
  sorry
```

**CUDA comparison:** ❌ No symbolic limits

**Difficulty:** Medium-Hard (3-4 months)

---

### 6. **Simplification / Computer Algebra** ⚠️

**Why it's missing:** Requires full CAS (Computer Algebra System).

**Can we add it?** ✅ **YES** - But very complex

**What it needs:**
```simple
# Future syntax:
val simplified = m{ simplify((x + 1)^2) }
# → x^2 + 2*x + 1

val factored = m{ factor(x^2 - 1) }
# → (x - 1)(x + 1)

val expanded = m{ expand((x + 1)(x - 1)) }
# → x^2 - 1

val collected = m{ collect(2*x + 3*x - x, x) }
# → 4*x
```

**Research required:**
- Term rewriting systems
- Pattern matching engine
- Normalization strategies
- Polynomial manipulation

**Lean4 comparison:**
```lean
-- Lean4 has ring tactics for simplification
example (x : ℝ) : (x + 1)^2 = x^2 + 2*x + 1 := by
  ring
```

**CUDA comparison:** ❌ No symbolic algebra

**Difficulty:** Very Hard (1+ year research project)

**Recommendation:** Use external CAS tools (SymPy, Mathematica) for now.

---

## ❌ **LOW PRIORITY / BY DESIGN - Should NOT Add**

### 7. **Imperative Logic in Expressions** ❌

**Why it's missing:** Math blocks are **pure expressions** by design.

**Should we add it?** ❌ **NO** - Contradicts design

**Reason:**
```simple
# ❌ BAD - This is NOT what m{} is for:
m{
    var sum = 0
    for i in 1..10:
        sum = sum + i^2
    sum
}

# ✅ GOOD - Use summation or regular code:
m{ sum(i, 1..10) i^2 }  # Mathematical notation
# OR
var sum = 0
for i in 1..10:
    sum = sum + i ** 2
```

**Lean4:** Has `do` notation for imperative-style code, but separate from pure expressions.

**CUDA:** Imperative by nature (C++ extension).

**Verdict:** Keep m{} pure, use regular Simple for imperative code.

---

### 8. **Side Effects (print, I/O)** ❌

**Why it's missing:** Purity required for correctness.

**Should we add it?** ❌ **NO** - Breaks referential transparency

**Reason:**
```simple
# ❌ BAD - Would break equational reasoning:
val x = m{
    print "Debug"  # Side effect!
    42
}

# Math blocks should be pure:
val a = m{ 2 + 2 }
val b = m{ 2 + 2 }
# We can replace 'b' with 'a' safely (referential transparency)
```

**Lean4:** Pure by default (side effects require `IO` monad).

**CUDA:** Allows side effects (but discouraged in device functions).

**Verdict:** Keep m{} pure. Use regular code for I/O.

---

### 9. **LaTeX Document Environments** ❌

**Why it's missing:** m{} is for computation, not typesetting.

**Should we add it?** ❌ **NO** - Wrong abstraction level

**Reason:**
```latex
% This is LaTeX's job, not m{}'s:
\begin{align}
  x + y &= 5 \\
  2x - y &= 1
\end{align}
```

**Instead:** Generate LaTeX from m{} expressions, assemble manually.

**Lean4:** No LaTeX environment support (generates LaTeX via tools).

**CUDA:** N/A (not a typesetting system).

**Verdict:** Keep m{} for computation, use LaTeX for document structure.

---

## 📊 **Comparison Summary**

### **Simple m{} vs. Lean4 vs. CUDA**

| Feature | Simple m{} (Current) | Simple (Future) | Lean4 | CUDA Math |
|---------|---------------------|-----------------|-------|-----------|
| **Numerical Computation** | ✅ Excellent | ✅ Excellent | ⚠️ Limited | ✅ Excellent |
| **Symbolic Diff** | ❌ No | ✅ Can add | ✅ Yes | ❌ No |
| **Symbolic Integration** | ❌ No | ⚠️ Very hard | ✅ Yes | ❌ No |
| **Limits** | ❌ No | ⚠️ Can add | ✅ Yes | ❌ No |
| **Special Functions** | ⚠️ Basic | ✅ Can add | ✅ Extensive | ⚠️ Some |
| **Simplification** | ❌ No | ⚠️ Very hard | ✅ Yes (tactics) | ❌ No |
| **Piecewise** | ❌ No | ✅ Easy to add | ✅ Yes | ✅ Yes |
| **LaTeX Rendering** | ✅ Yes | ✅ Yes | ⚠️ Via tools | ❌ No |
| **Theorem Proving** | ❌ No | ❌ No | ✅ Core feature | ❌ No |
| **GPU Acceleration** | ❌ No | ⚠️ Possible | ❌ No | ✅ Core feature |
| **Deep Learning** | ✅ Excellent | ✅ Excellent | ⚠️ Limited | ✅ Excellent |

**Different purposes:**
- **Simple m{}**: Numerical computation + LaTeX export for papers
- **Lean4**: Theorem proving + symbolic mathematics
- **CUDA**: High-performance numerical computation on GPU

---

## 🎯 **Research Priorities for Simple**

### **Tier 1: High Impact, Feasible** (Next 6 months)

1. ✅ **Symbolic differentiation** - Enable `diff(expr, var)`
2. ✅ **Piecewise functions** - Add `cases()` or `if-then-else`
3. ✅ **Special functions** - Add `erf`, `gamma`, `beta`

### **Tier 2: Medium Impact** (Next 1-2 years)

4. ⚠️ **Limits** - Basic limit computation
5. ⚠️ **Partial derivatives** - Multi-variable calculus
6. ⚠️ **More special functions** - Bessel, elliptic, etc.

### **Tier 3: Research Projects** (Long-term)

7. ⚠️ **Symbolic integration** - Very hard, consider external tools first
8. ⚠️ **Simplification** - CAS features, major undertaking

### **Not Planned:**

- ❌ Imperative logic in m{}
- ❌ Side effects in m{}
- ❌ LaTeX document structure

---

## 🚀 **Recommended Approach**

### **Short-term (3-6 months):**

1. **Add symbolic differentiation**
   - Implement basic differentiation rules
   - Support `diff(expr, var)` syntax
   - Render to LaTeX: `\frac{d}{dx}(...)`

2. **Add piecewise syntax**
   - Support `cases()` function
   - Render to `\begin{cases}...\end{cases}`

3. **Expand special functions**
   - Add `erf`, `gamma`, `beta` (most used in ML/stats)
   - Use existing C library implementations

### **Medium-term (1-2 years):**

4. **Add limit computation**
   - Basic direct substitution
   - L'Hôpital's rule
   - Asymptotic analysis

5. **Improve symbolic capabilities**
   - Basic simplification (collect terms)
   - Polynomial manipulation
   - Trigonometric identities

### **Long-term (Beyond 2 years):**

6. **Consider full CAS integration**
   - Partner with SymPy/Sage as backend
   - FFI to external symbolic engines
   - Or build minimal CAS focused on DL needs

---

## 💡 **Conclusion**

**Yes, research can add many "missing" features!**

### **Feasible to add:**
- ✅ Symbolic differentiation (high priority)
- ✅ Special functions (easy)
- ✅ Piecewise functions (easy)
- ⚠️ Limits (medium difficulty)
- ⚠️ Symbolic integration (very hard)
- ⚠️ Simplification (very hard)

### **By design (should not add):**
- ❌ Imperative logic
- ❌ Side effects
- ❌ LaTeX document structure

### **Comparison:**
- **Lean4** has more symbolic features (theorem prover focus)
- **CUDA** has more numerical features (GPU computation focus)
- **Simple m{}** balances both + targets deep learning + LaTeX export

**Next step:** Implement Tier 1 features (symbolic diff, piecewise, special functions) in next 6 months.
