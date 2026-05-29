# Simple ML Guide — std.ml Linear Models and Metrics

## 1. Overview

`std.ml` provides sklearn-style estimator types for linear regression
and evaluation metrics, written entirely in Simple.

The library is split into two modules:

| Module | Contents |
|--------|----------|
| `std.common.science_math.ml_linear` | `LinearRegression`, `Ridge`, `ml_predict_linear`, `ml_mse` |
| `std.common.science_math.ml_metrics` | `ml_mse_metric`, `ml_mae_metric`, `ml_r2`, `ml_rmse`, `ml_accuracy_int`, `ml_accuracy_float`, `ConfusionMatrix2` |

**Design note:** The model types are *consumer* classes — they store and
apply fitted coefficients but do not solve the normal equation themselves.
Callers obtain coefficients from `std.linalg.solve` (which wraps LAPACK
`gesv`) and inject them via `set_coef`.

---

## 2. Imports

```simple
use std.common.science_math.ml_linear.{LinearRegression, Ridge, ml_predict_linear, ml_mse}

use std.common.science_math.ml_metrics.{
    ml_mse_metric, ml_mae_metric, ml_r2, ml_rmse,
    ml_accuracy_int, ml_accuracy_float, ConfusionMatrix2
}
```

---

## 3. Linear Regression

### Construction

```simple
val model = LinearRegression.new()
```

`new()` returns an unfitted model (`is_fitted()` returns `false`).

### Injecting coefficients

After solving `(XᵀX)β = Xᵀy` with `std.linalg.solve`, inject the result:

```simple
var model = LinearRegression.new()
model.set_coef([2.0, 0.5], 1.0)   # coef vector, intercept
```

`set_coef` marks the model as fitted.  Query state with:

```simple
model.is_fitted()    # -> bool
model.coef()         # -> [f64]
model.intercept()    # -> f64
```

### Single-row prediction

```simple
val y = model.predict([3.0, 4.0])   # dot(coef, x) + intercept
```

### Batch prediction

```simple
val preds = model.predict_batch([[0.0], [1.0], [2.0]])   # -> [f64]
```

---

## 4. Ridge Regression

Ridge adds L2 regularisation: the normal equation becomes
`(XᵀX + αI)β = Xᵀy`.  The `alpha` parameter is stored for
documentation and auditing; the caller is responsible for
incorporating it into the solve step.

```simple
var model = Ridge.new(0.1)         # alpha = 0.1
model.set_coef([1.5, -0.3], 0.0)
val y = model.predict([2.0, 1.0])
```

Accessor methods are identical to `LinearRegression`, plus:

```simple
model.alpha()   # -> f64
```

`predict` and `predict_batch` behave identically to `LinearRegression`.

---

## 5. Metrics

All metric functions operate on plain `[f64]` or `[int]` slices —
no matrix types required.

### Regression metrics

| Function | Signature | Notes |
|----------|-----------|-------|
| `ml_mse_metric` | `(y_true: [f64], y_pred: [f64]) -> f64` | Mean Squared Error |
| `ml_mae_metric` | `(y_true: [f64], y_pred: [f64]) -> f64` | Mean Absolute Error |
| `ml_r2` | `(y_true: [f64], y_pred: [f64]) -> f64` | R² coefficient of determination |
| `ml_rmse` | `(y_true: [f64], y_pred: [f64]) -> f64` | Root Mean Squared Error |

```simple
val mse  = ml_mse_metric([1.0, 2.0, 3.0], [1.1, 1.9, 3.2])
val r2   = ml_r2([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])   # 1.0 = perfect
val rmse = ml_rmse([0.0, 1.0], [0.5, 0.5])
```

Edge cases: empty inputs return `0.0`.  When all true values are
identical (`ss_tot == 0`) and predictions are not perfect, `ml_r2`
returns `0.0`.

### Classification accuracy

```simple
val acc = ml_accuracy_int([1, 0, 1, 1], [1, 0, 0, 1])    # integer labels
val acc = ml_accuracy_float([1.0, 0.0], [1.0, 1.0])       # float labels
```

Both return a `f64` fraction in `[0.0, 1.0]`.

### Binary confusion matrix

`ConfusionMatrix2` works with integer labels `0` and `1`.

```simple
val cm = ConfusionMatrix2.compute([1, 1, 0, 0], [1, 0, 0, 0])
val p  = cm.precision()   # -> f64
val r  = cm.recall()      # -> f64
val f1 = cm.f1()          # harmonic mean of precision and recall
```

---

## 6. Free Function Helpers (ml_linear)

These helpers are exported from `ml_linear` alongside the class types.

### `ml_predict_linear`

```simple
fn ml_predict_linear(coef: [f64], intercept: f64, x_row: [f64]) -> f64
```

Computes `dot(coef, x_row) + intercept` without constructing a model
object.  Useful for one-off predictions or custom evaluation loops.

```simple
val y = ml_predict_linear([2.0, 3.0], 1.0, [4.0, 5.0])  # 2*4 + 3*5 + 1 = 24
```

### `ml_mse`

A lightweight MSE helper co-located in `ml_linear`:

```simple
fn ml_mse(y_true: [f64], y_pred: [f64]) -> f64
```

Equivalent to `ml_mse_metric` from `ml_metrics`.  Import whichever
module you already depend on.

---

## 7. Integration with linalg / BLAS

`std.ml` is a *consumer* layer; it delegates all linear algebra to
`std.linalg`.  The typical end-to-end flow is:

1. Build the design matrix `X` and target vector `y` as `NDArray` or
   `[f64]` slices.
2. Call `std.linalg.solve` (wraps LAPACK `gesv`) to obtain `β` and
   the intercept.
3. Call `model.set_coef(beta, intercept)` to bind the result.
4. Call `model.predict` or `model.predict_batch` for inference.

Ridge adds `α` to the diagonal of `XᵀX` before passing the system to
`linalg.solve`; that modification happens in caller code, not inside
the `Ridge` class itself.

The `rt_math_sqrt` extern (used by `ml_rmse`) is provided by the
Simple runtime and requires no separate setup.
