# Numerical Methods Modules

This directory contains 11 focused modules refactored from the original 2,434-line `numerical_methods_utils.spl` file.

## Module Structure

| Module | Lines | Purpose |
|--------|-------|---------|
| **error_analysis.spl** | 86 | Constants, error calculation, tolerance checking, condition numbers |
| **polynomials.spl** | 90 | Horner's method, derivatives, polynomial arithmetic |
| **root_finding.spl** | 343 | Bisection, Newton-Raphson, secant, Brent, fixed-point, Muller |
| **integration.spl** | 254 | Trapezoidal, Simpson, Romberg, Gaussian quadrature, adaptive, Monte Carlo |
| **differentiation.spl** | 144 | Forward/backward/central differences, Richardson, gradients, Hessian |
| **interpolation.spl** | 152 | Linear, Lagrange, Newton divided differences, cubic splines |
| **ode_solvers.spl** | 232 | Euler, RK2/RK4, Adams-Bashforth, backward Euler, trapezoidal |
| **linear_systems.spl** | 510 | Gaussian elimination, LU/Cholesky/QR, Jacobi, Gauss-Seidel |
| **eigenvalues.spl** | 406 | Power iteration, inverse power, vector/matrix norms |
| **curve_fitting.spl** | 345 | Least squares, polynomial fitting, RSS, R², optimization helpers |
| **special_functions.spl** | 251 | Factorial, binomial, gamma, log/exp/sqrt, trig, error function |
| **Total** | **2,813** | **All modules** |

## Facade Pattern

The main file `src/std/numerical_methods_utils.spl` (35 lines) acts as a facade that:
- Imports all 11 submodules
- Re-exports all functions for 100% backward compatibility
- Maintains the original API surface

## Refactoring Metrics

- **Original file:** 2,434 lines
- **New facade:** 35 lines (98.6% reduction)
- **Total modules:** 2,813 lines (includes headers/documentation)
- **Average module size:** 256 lines (down from 2,434)
- **Largest module:** 510 lines (linear_systems.spl)
- **Smallest module:** 86 lines (error_analysis.spl)
- **Overhead:** 379 lines (15.6%) for improved documentation and structure

## Usage

All original imports continue to work:

```simple
# Still works - imports from facade
from numerical_methods_utils import {nm_bisection, nm_simpson, nm_rk4_classic}

# Also works - imports from specific modules
from numerical_methods.root_finding import {nm_bisection}
from numerical_methods.integration import {nm_simpson}
from numerical_methods.ode_solvers import {nm_rk4_classic}
```

## Design Decisions

1. **Module boundaries follow algorithmic categories** - Each module groups related numerical methods
2. **Self-contained modules** - Some helper functions duplicated to avoid circular dependencies
3. **Clear headers** - Each module documents its purpose and contents
4. **Export all** - All modules use `export *` for simplicity
5. **No logic changes** - Pure structural refactoring, no algorithm modifications

## Benefits

- **Easier navigation:** Find functions by category, not line number
- **Better maintainability:** Changes isolated to relevant modules
- **Clearer organization:** Related algorithms grouped together
- **Improved documentation:** Module headers explain purpose and scope
- **Reduced cognitive load:** Smaller files easier to understand
