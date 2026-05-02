# scilib_port_ml.md — std.ml Task List (v1.1)

**Phase:** v1.1 (begins after v1 acceptance gates pass)
**Area:** `std.ml` — sklearn-shape estimators, preprocessing, model selection, metrics
**Physical location:** `src/lib/gc_async_mut/ml/`
**Import:** `use std.ml`
**Scope:** DISJOINT from ndarray, blas, lapack, cuda_fortran, df, math_block, perf_sugar agents

**Hard prereqs before any task here:**
- v1 acceptance gates ALL green (see arch §12: NDArray, linalg, PERF-SUGAR-001 fixed, bootstrap rebuild done)
- T-DF-01 through T-DF-08 (DataFrame + Series<T> + from_ndarray) complete — Pipeline needs DataLoader
- T-NDARRAY-* broadcasting engine complete — all fit()/transform() inputs are NDArray<Float64>
- T-LAPACK-* gesv + gesvd complete — LinearRegression fit() and Ridge fit() call gesv/dgels

**Naming rules (enforce throughout):**
- NO inheritance — all extension via traits and composition only
- `fit`, `transform`, `predict`, `score` are trait methods, never free functions
- `sum`/`mean`/`norm` on arrays are NDArray methods — never add free-function aliases in std.ml
- Re-export `common/pure/nn/loss.spl` and `common/pure/nn/norm.spl`; DO NOT redefine
- `DType`, `Device` re-exported from std.ndarray (which re-exports from tensor.spl); DO NOT redefine
- `Device` re-export path: std.ml → std.ndarray → tensor.spl
- cuML: deferred to v2. No cuML code in v1.1.

**Anti-patterns forbidden:**
- Inheritance-style Estimator base class or abstract class
- DataFrame in math{} blocks (string-keyed ops incompatible with MathExpr)
- Heterogeneous dynamic list for Pipeline steps (no dyn dispatch in Simple v1.1)
- cuML bindings (RAPIDS C++ ABI, deferred to v2)
- Primitive types in any public API signature (`f64`, `i64`, etc.)
- `skip()` in specs; TODO→NOTE conversions

---

## Group 1: Foundation — Traits and Types

### T-ML-01: MlError enum and std.ml.types module
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/types.spl`
**Deps:** T-NDARRAY-types (NDArray<Float64>, Shape, Index, Float64 wrappers available)

Define all public ML types that are not models or traits:

- `enum MlError { NotFitted, DimensionMismatch(Shape, Shape), ConvergenceFailure(Index), InvalidInput(text), UnsupportedDType(DType) }`
- Re-export `DType` and `Device` from `std.ndarray` (no redefinition)
- Re-export `nn/loss.spl` exports under `std.ml.loss` namespace
- Re-export `nn/norm.spl` exports (`BatchNorm`, `LayerNorm`) under `std.ml.norm` namespace
- `struct FitState { _is_fitted: Bool }` — shared fitted-guard mixin for stateful transformers
- `enum NormOrd { L1, L2, Inf }` if not already in std.linalg (check; reuse if present)

No primitive types in any field or signature. All struct fields use typed wrappers.

Spec: `test/ml/types_spec.spl` — construct each error variant, verify MlError.DimensionMismatch carries Shape args, verify re-exports resolve without ambiguity.

---

### T-ML-02: Estimator and Transformer traits
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/traits.spl`
**Deps:** T-ML-01

Define the two core traits. No inheritance. Composition only.

```
trait Estimator:
    fn fit(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Unit, MlError>
    fn predict(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
    fn score(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Float64, MlError>

trait Transformer:
    fn fit(self, x: NDArray<Float64>) -> Result<Unit, MlError>
    fn transform(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
    fn fit_transform(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
```

`fit_transform` default body: call `self.fit(x)?` then `self.transform(x)`. Implementors may override.

Note: `score` on a `Transformer` is not required; it is an `Estimator`-only method. If a type wants both traits it implements both independently (composition, not mixin inheritance).

Spec: `test/ml/traits_spec.spl` — implement a trivial `IdentityTransformer` struct conforming to `Transformer` trait; verify `fit_transform` default impl fires without override; verify `MlError.NotFitted` is returned from `transform` before `fit`.

---

## Group 2: Preprocessing

### T-ML-03: StandardScaler
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/preprocessing/standard_scaler.spl`
**Deps:** T-ML-02, T-NDARRAY-ops (NDArray.mean/std as methods)

```
struct StandardScaler:
    _with_mean: Bool
    _with_std:  Bool
    _mean_:     Option<NDArray<Float64>>   # per-feature mean; None until fit()
    _std_:      Option<NDArray<Float64>>   # per-feature std; None until fit()
```

- `fit(x)`: compute column-wise `x.mean(axis=Index(0))` and `x.std(axis=Index(0))`; store in `_mean_`/`_std_`
- `transform(x)`: guard NotFitted; subtract mean if `_with_mean`; divide by std if `_with_std`; std=0 columns set to Float64(0.0) (not NaN, no primitive)
- `inverse_transform(x)`: reverse the scaling
- All ops use NDArray methods (axis-parameterised); no free-function sum/mean/std at ml level
- PERF-SUGAR-003 note: if interpreter is slow on NDArray<Float64> generic dispatch, document observed cost in `scilib_perf_sugar.md` entry PERF-SUGAR-003 and proceed (watchful, not blocking)

Spec: `test/ml/standard_scaler_spec.spl` — fit on 3×2 matrix, verify mean_ shape is (2,), transform produces zero-mean unit-variance columns, inverse_transform recovers original within Float64 tolerance.

---

### T-ML-04: MinMaxScaler
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/preprocessing/minmax_scaler.spl`
**Deps:** T-ML-02, T-NDARRAY-ops

```
struct MinMaxScaler:
    _feature_range: (Float64, Float64)   # default (Float64(0.0), Float64(1.0))
    _min_:          Option<NDArray<Float64>>
    _scale_:        Option<NDArray<Float64>>
    _data_min_:     Option<NDArray<Float64>>
    _data_max_:     Option<NDArray<Float64>>
```

- `fit(x)`: compute column min/max; compute scale = (range_max - range_min) / (data_max - data_min); zero-range columns → scale = Float64(1.0)
- `transform(x)`: guard NotFitted; apply scale and shift
- `inverse_transform(x)`: reverse

Spec: `test/ml/minmax_scaler_spec.spl` — fit on known matrix, verify output range is [0,1], verify inverse recovers original.

---

### T-ML-05: LabelEncoder
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/preprocessing/label_encoder.spl`
**Deps:** T-ML-02, T-NDARRAY-ops, T-DF-Series (Series<T> for label storage)

```
struct LabelEncoder:
    _classes_: Option<NDArray<text>>   # sorted unique labels after fit()
```

- Input: `NDArray<text>` (categorical labels as text, no raw strings in public sig beyond `text` type)
- `fit(y: NDArray<text>)`: collect unique labels, sort lexicographically, store in `_classes_`
- `transform(y: NDArray<text>) -> Result<NDArray<Index>, MlError>`: map each label to its sorted position; unknown label → `MlError.InvalidInput`
- `inverse_transform(y: NDArray<Index>) -> Result<NDArray<text>, MlError>`: reverse lookup; out-of-range index → `MlError.InvalidInput`
- No primitive integer output — return type is `NDArray<Index>`

Spec: `test/ml/label_encoder_spec.spl` — fit ["cat","dog","bird"], verify transform("dog")=Index(1), inverse_transform(Index(0))="bird", unknown label returns Err.

---

### T-ML-06: OneHotEncoder
**Phase:** v1.1
**Effort:** 2 days
**File:** `src/lib/gc_async_mut/ml/preprocessing/one_hot_encoder.spl`
**Deps:** T-ML-02, T-NDARRAY-ops, T-ML-05 (shares label-sorted category logic)

**High-risk task** — sparse output and unknown-category handling are the two hard sub-problems.

```
struct OneHotEncoder:
    _categories_:      Option<[NDArray<text>]>   # per-feature sorted categories
    _handle_unknown:   UnknownHandling            # enum: Error | Ignore | InfrequentIfExist
    _sparse_output:    Bool                       # v1.1: dense only; sparse deferred to v2
```

- `enum UnknownHandling { Error, Ignore }` — `InfrequentIfExist` deferred to v2
- **v1.1 scope: dense output only.** Sparse matrix type deferred to v2. If `_sparse_output = Bool(true)` is requested, return `MlError.InvalidInput` with message "sparse output deferred to v2".
- `fit(x: NDArray<text>)`: per-column, collect sorted unique categories; store in `_categories_`
- `transform(x: NDArray<text>) -> Result<NDArray<Float64>, MlError>`: for each column expand to one-hot; unknown category: if `Error` → return Err; if `Ignore` → all-zeros row for that feature
- Output shape: `(n_samples, sum(len(cats_per_col)))`
- `inverse_transform(x: NDArray<Float64>) -> Result<NDArray<text>, MlError>`: argmax per feature block → label lookup; all-zeros (from Ignore) → text literal `"<unknown>"`
- `get_feature_names_out() -> [text]`: returns list of `"feature_N_label"` strings

**Risk mitigation:**
- Do not attempt sparse NDArray in v1.1; return dense Float64 matrix only
- Do not use `Option<NDArray<text>>` with raw text primitives in field; `text` is the Simple text type (non-primitive)
- Record PERF-SUGAR-003 observation if generic `NDArray<text>` dispatch is slow in interpreter

Spec: `test/ml/one_hot_encoder_spec.spl` — fit 2-column text array, verify output shape, verify Ignore mode emits zeros for unknown, verify Error mode returns Err, verify inverse_transform round-trips.

---

## Group 3: Model Selection

### T-ML-07: train_test_split
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/model_selection/split.spl`
**Deps:** T-ML-01, T-NDARRAY-ops (NDArray slicing, row indexing)

```
fn train_test_split<T>(
    x:         NDArray<T>,
    y:         NDArray<T>,
    test_size: Float64,
    seed:      Index
) -> Result<(NDArray<T>, NDArray<T>, NDArray<T>, NDArray<T>), MlError>
```

Returns `(x_train, x_test, y_train, y_test)`.

- `test_size` must be in (Float64(0.0), Float64(1.0)); else `MlError.InvalidInput`
- Shuffle row indices using seeded RNG (compose `std.common.random_utils` or `nogc_sync_mut/src/core/random.spl` — reuse, do not reimplement)
- Split at floor(n_samples * (1 - test_size))
- Return NDArray sliced views (O(1) if strided views available; copy-based fallback if PERF-SUGAR-005 not yet landed — document as PERF-SUGAR-005 observed)
- No variadic arrays (Python's `*arrays` form) — Simple lacks that; accept x and y explicitly; multi-array variant is a follow-up
- Generic `<T>` dispatch: note PERF-SUGAR-003; proceed

Spec: `test/ml/train_test_split_spec.spl` — 100-row array, test_size=Float64(0.2), verify row counts sum to 100, verify seed reproducibility.

---

### T-ML-08: KFold
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/model_selection/kfold.spl`
**Deps:** T-ML-01, T-NDARRAY-ops

```
struct KFold:
    _n_splits: Index
    _shuffle:  Bool
    _seed:     Index

fn KFold.new(n_splits: Index, shuffle: Bool, seed: Index) -> KFold
fn KFold.split(self, x: NDArray<Float64>) -> [(NDArray<Index>, NDArray<Index>)]
```

- `split` returns a list of `(train_indices, test_indices)` pairs (one per fold)
- Each fold: test indices are a contiguous block of size floor(n / n_splits) or ceil; train = complement
- Shuffle: permute row indices before splitting (seeded RNG same as T-ML-07)
- n_splits < Index(2) → `MlError.InvalidInput` (return in a Result-wrapping variant or panic — use Result)
- Return type is `[(NDArray<Index>, NDArray<Index>)]` — list of index-pair tuples; no primitive int arrays

Spec: `test/ml/kfold_spec.spl` — n=10, n_splits=5: verify 5 pairs, each test set size 2, union of all test sets = all row indices (no overlap, no gap).

---

### T-ML-09: StratifiedKFold
**Phase:** v1.1
**Effort:** 2 days
**File:** `src/lib/gc_async_mut/ml/model_selection/stratified_kfold.spl`
**Deps:** T-ML-08, T-ML-05 (label sorting logic), T-NDARRAY-ops

**High-risk task** — label-frequency equalization across folds requires sort+count+interleave, which is non-trivial and exercises NDArray<Index> and NDArray<text> together.

```
struct StratifiedKFold:
    _n_splits: Index
    _shuffle:  Bool
    _seed:     Index

fn StratifiedKFold.new(n_splits: Index, shuffle: Bool, seed: Index) -> StratifiedKFold
fn StratifiedKFold.split(
    self,
    x: NDArray<Float64>,
    y: NDArray<text>
) -> Result<[(NDArray<Index>, NDArray<Index>)], MlError>
```

Algorithm:
1. Group row indices by class label (use sorted unique labels from LabelEncoder logic — reuse, do not copy)
2. For each class, distribute indices across folds as evenly as possible (interleave)
3. Assemble train/test splits per fold from distributed indices
4. If any class has fewer than `_n_splits` samples → `MlError.InvalidInput`

Risk: step 2 requires per-class index grouping — a mini-groupby over NDArray<Index>. Do NOT import std.df for this; implement a local `group_by_label` helper using NDArray operations only (sort + scan). This keeps std.ml disjoint from std.df at the implementation level (even though df is a sibling area).

Spec: `test/ml/stratified_kfold_spec.spl` — 12 samples, 3 classes (4 each), n_splits=3: verify each fold test set has exactly 1 sample per class (4 total), train set 8 samples; verify no index appears in both train and test for the same fold.

---

### T-ML-10: cross_val_score
**Phase:** v1.1
**Effort:** 2 days
**File:** `src/lib/gc_async_mut/ml/model_selection/cross_val.spl`
**Deps:** T-ML-08 (KFold), T-ML-02 (Estimator trait), T-ML-15 (metrics.mse / metrics.accuracy), T-NDARRAY-ops

**High-risk task** — requires "clone per fold" semantics. Simple has no stdlib clone trait; each Estimator must be re-initialized per fold using its constructor, not a generic clone operation. This is the key design decision for this task.

```
fn cross_val_score<E: Estimator>(
    estimator_factory: fn() -> E,
    x:                 NDArray<Float64>,
    y:                 NDArray<Float64>,
    cv:                KFold,
    scoring:           ScoringFn
) -> Result<NDArray<Float64>, MlError>

enum ScoringFn { Mse | Accuracy | R2 | Custom(fn(NDArray<Float64>, NDArray<Float64>) -> Float64) }
```

**Clone-per-fold design:**
- Caller passes `estimator_factory: fn() -> E` instead of a single estimator instance
- Each fold calls `estimator_factory()` to get a fresh estimator; no clone/copy needed
- This is the correct Simple-idiomatic solution: factory function replaces clone semantics
- Python's `clone(estimator)` does not map to Simple's no-inheritance world; document this design decision in a comment block at the top of the file

Algorithm per fold:
1. `let est = estimator_factory()`
2. `est.fit(x_train, y_train)?`
3. `let y_pred = est.predict(x_test)?`
4. Apply scoring function to `(y_test, y_pred)`; store `Float64` score
5. Return `NDArray<Float64>` of scores (one per fold)

PERF-SUGAR-003 note: generic `<E: Estimator>` dispatch in interpreter mode may be slow. If test runtime exceeds 30s for n=5 folds, record observed cost in PERF-SUGAR-003 entry and continue.

Spec: `test/ml/cross_val_score_spec.spl` — use `LinearRegression` as estimator (T-ML-12), synthetic 20×1 data with known linear relationship, 5-fold CV with R2 scoring; verify all 5 scores are Float64 and NDArray shape is (5,).

---

## Group 4: Pipeline and ColumnTransformer

### T-ML-11: Pipeline (tuple-of-steps)
**Phase:** v1.1
**Effort:** 2 days
**File:** `src/lib/gc_async_mut/ml/pipeline.spl`
**Deps:** T-ML-02 (traits), T-ML-03 (StandardScaler as first concrete user)

**High-risk task** — Simple lacks heterogeneous-type dynamic lists and dyn dispatch. Pipeline<Steps> uses tuple-of-steps generic but interpreter-mode monomorphization is limited (PERF-SUGAR-003).

**Design (from arch §9):**

```
struct Pipeline<Steps>:
    _steps: Steps   # tuple, e.g. (StandardScaler, LinearRegression)

fn Pipeline.new<Steps>(steps: Steps) -> Pipeline<Steps>
fn Pipeline.fit<Steps>(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Unit, MlError>
fn Pipeline.predict<Steps>(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
```

**Implementation strategy for v1.1 (no dyn dispatch):**
- Provide hand-specialized pipeline wrappers for the two most common shapes:
  - `Pipeline2<T: Transformer, E: Estimator>` — one transformer + one estimator
  - `Pipeline3<T1: Transformer, T2: Transformer, E: Estimator>` — two transformers + one estimator
- Name these `Pipeline2` and `Pipeline3` in the public API for v1.1
- The generic `Pipeline<Steps>` tuple form is defined but carries a compiler warning that it requires monomorphization; spec tests use `Pipeline2`/`Pipeline3`
- `Pipeline2.fit`: call `t.fit_transform(x)?` → pass result to `e.fit(result, y)?`
- `Pipeline2.predict`: call `t.transform(x)?` → pass to `e.predict(result)?`
- `Pipeline3.fit`: chain two `fit_transform` calls then estimator `fit`
- Do NOT attempt runtime step dispatch via type-erased list; no dyn Estimator, no vtable
- File a feature request in `compiler_requests.md` for "heterogeneous tuple dispatch for Pipeline" once PERF-SUGAR-003 is resolved, so v2 can use the cleaner `Pipeline<Steps>` form

Spec: `test/ml/pipeline_spec.spl` — `Pipeline2<StandardScaler, LinearRegression>`: fit on synthetic data, verify predict returns NDArray<Float64> of correct shape, verify scaler state is set after fit. Use SIMPLE_BLAS_BACKEND=mock.

**ColumnTransformer (partial — v1.1 scope):**

```
struct ColumnTransformerStep<T: Transformer>:
    _name:    text
    _trans:   T
    _cols:    [Index]   # column indices to apply transformer to (no Symbol lookup — df not required)

struct ColumnTransformer2<T1: Transformer, T2: Transformer>:
    _steps:    (ColumnTransformerStep<T1>, ColumnTransformerStep<T2>)
    _remainder: RemainderPolicy

enum RemainderPolicy { Drop | Passthrough }
```

- `ColumnTransformer2.fit(x)`: apply each step's transformer to its column slice; store fitted transformers
- `ColumnTransformer2.transform(x)`: apply each transformer to its columns; concatenate results horizontally; handle remainder
- Column indices use `[Index]` (typed), not `[i64]`
- More than 2 transformer steps deferred to v2 (same tuple-dispatch limitation as Pipeline)

Spec: `test/ml/column_transformer_spec.spl` — two-column matrix, step1=StandardScaler on col 0, step2=MinMaxScaler on col 1, verify output shape and column independence.

---

## Group 5: Models

### T-ML-12: LinearRegression
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/linear/linear_regression.spl`
**Deps:** T-ML-02, T-LAPACK-gesv (linalg.gesv or linalg.solve), T-NDARRAY-ops

```
struct LinearRegression:
    _fit_intercept: Bool
    _coef_:         Option<NDArray<Float64>>
    _intercept_:    Option<Float64>
```

- `fit(x, y)`: if `_fit_intercept` = true, prepend column of Float64(1.0) to x; solve normal equation `(XᵀX)β = Xᵀy` via `linalg.gesv`; store `_coef_` and `_intercept_`
- `predict(x)`: guard NotFitted; compute `x @ _coef_ + _intercept_` using `linalg.gemv` or explicit NDArray ops; return `NDArray<Float64>`
- `score(x, y)`: call `metrics.r2(y, self.predict(x)?)` (T-ML-15)
- Cross-area dep: `T-LAPACK-gesv` for the normal equation solve

Spec: `test/ml/linear_regression_spec.spl` — fit on `y = 2x + 1` with noise, verify coef_ close to Float64(2.0), predict on new x, verify r2 > Float64(0.99). SIMPLE_BLAS_BACKEND=mock (mock gesv returns identity-like solution; spec must use data where mock is still valid — use pre-solved fixture).

---

### T-ML-13: Ridge
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/linear/ridge.spl`
**Deps:** T-ML-02, T-LAPACK-gesv, T-NDARRAY-ops

```
struct Ridge:
    _alpha:         Float64
    _fit_intercept: Bool
    _coef_:         Option<NDArray<Float64>>
    _intercept_:    Option<Float64>
```

- `fit(x, y)`: closed-form `(XᵀX + αI)⁻¹Xᵀy` via `linalg.gesv` (solve `(XᵀX + αI)β = Xᵀy` directly; do not invert explicitly)
- If `_fit_intercept`, center x and y before fit (subtract column means of x, mean of y); restore intercept after
- `predict(x)` and `score(x, y)`: same pattern as LinearRegression
- Cross-area dep: T-LAPACK-gesv

Spec: `test/ml/ridge_spec.spl` — verify Ridge with alpha=Float64(0.0) produces same coef_ as LinearRegression on same data (to within tolerance); verify alpha=Float64(1000.0) shrinks coef_ toward zero. Use mock backend with pre-solved fixtures.

---

### T-ML-14: LogisticRegression, Lasso, DecisionTree, KMeans, KNeighbors — v1.1 stub or punt
**Phase:** v1.1
**Effort:** ≤1 day (stubs only)
**File:** `src/lib/gc_async_mut/ml/linear/logistic_regression.spl`, `lasso.spl`; `src/lib/gc_async_mut/ml/tree/decision_tree.spl`; `src/lib/gc_async_mut/ml/cluster/kmeans.spl`; `src/lib/gc_async_mut/ml/neighbors/knn.spl`

**Scope for v1.1:** Struct definition + constructor + unimplemented `fit`/`predict` returning `MlError.InvalidInput("not implemented in v1.1")`. This satisfies the "no TODO→NOTE" rule: the error is real and explicit, not suppressed.

**Why stubs and not full implementation:**
- `LogisticRegression`: requires iterative L-BFGS or SGD solver — multi-week project; needs gradient computation infrastructure not in scope
- `Lasso`: requires coordinate descent convergence loop — similar scope
- `DecisionTreeRegressor`/`DecisionTreeClassifier`: recursive tree construction — separate data structure, not just linalg calls
- `KMeans`: Lloyd iteration with mutable RNG state — feasible but out of v1.1 priority
- `KNeighborsClassifier`: brute-force O(n²) is feasible; KD-tree is not — file a note for v2

**Stubs must:**
- Conform to `Estimator` trait (implement all three methods: `fit`, `predict`, `score`)
- Return `MlError.InvalidInput("v1.1 stub — implement in v2")` from `fit`
- Have a `new()` constructor that compiles without error
- Have at least one spec asserting the Err return (so the stub is testable)

Spec: `test/ml/stubs_spec.spl` — construct each stub model, call fit, assert Err(MlError.InvalidInput) is returned.

---

## Group 6: Metrics

### T-ML-15: std.ml.metrics module
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/metrics.spl`
**Deps:** T-ML-01, T-NDARRAY-ops (NDArray.sum, NDArray.mean as methods)

All metrics are free functions in the `std.ml.metrics` sub-namespace. They do not conflict with `std.math` scalar helpers because they operate on `NDArray<Float64>` not on scalar `Float64` — different type, different namespace.

```
fn mse(y_true: NDArray<Float64>, y_pred: NDArray<Float64>) -> Result<Float64, MlError>
fn r2(y_true: NDArray<Float64>, y_pred: NDArray<Float64>) -> Result<Float64, MlError>
fn accuracy<T>(y_true: NDArray<T>, y_pred: NDArray<T>) -> Result<Float64, MlError>
fn confusion_matrix<T>(
    y_true:    NDArray<T>,
    y_pred:    NDArray<T>,
    normalize: Bool
) -> Result<NDArray<Float64>, MlError>
fn classification_report<T>(
    y_true:       NDArray<T>,
    y_pred:       NDArray<T>,
    target_names: [text]
) -> Result<text, MlError>
```

Implementation notes:
- `mse`: `mean((y_true - y_pred)^2)` — use NDArray subtraction and `.mean()` method; result wrapped in `Result` to propagate shape mismatch
- `r2`: `1 - ss_res/ss_tot`; `ss_res = sum((y_true-y_pred)^2)`, `ss_tot = sum((y_true - mean(y_true))^2)`; if `ss_tot == Float64(0.0)` return Float64(1.0) if predictions perfect, else Float64(0.0)
- `accuracy<T>`: element-wise equality count / n; generic T requires NDArray<T>.eq comparison — note PERF-SUGAR-003 if slow
- `confusion_matrix<T>`: build `(n_classes × n_classes)` NDArray<Float64>; classes derived from union of unique values in y_true and y_pred (reuse LabelEncoder logic); normalize=true divides each row by row sum
- `classification_report<T>`: per-class precision/recall/F1 computed from confusion matrix; text formatting using `std.common.text` (compose, do not reimplement string ops)
- No free-function `sum`/`mean` used at module scope — always called as `.sum()` / `.mean()` on NDArray instance

Spec: `test/ml/metrics_spec.spl`:
- `mse`: y_true=[1,2,3], y_pred=[1,2,3] → Float64(0.0); y_pred=[2,3,4] → Float64(1.0)
- `r2`: perfect prediction → Float64(1.0); mean prediction → Float64(0.0)
- `accuracy<Index>`: 3/4 correct → Float64(0.75)
- `confusion_matrix<text>`: 2-class, verify diagonal counts

---

## Group 7: Re-exports and Module Entry Point

### T-ML-16: std.ml mod.spl — facade, re-exports, module wiring
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `src/lib/gc_async_mut/ml/mod.spl`
**Deps:** T-ML-01 through T-ML-15

Assemble the public surface:

```
# Re-exports from existing modules (DO NOT redefine)
pub use common.pure.nn.loss.*          # loss.spl exports
pub use common.pure.nn.norm.*          # norm.spl exports (BatchNorm, LayerNorm)

# Re-exports from std.ndarray (which re-exports from tensor.spl)
pub use std.ndarray.DType
pub use std.ndarray.Device

# std.ml public surface
pub use ml.types.{ MlError, FitState }
pub use ml.traits.{ Estimator, Transformer }
pub use ml.preprocessing.standard_scaler.StandardScaler
pub use ml.preprocessing.minmax_scaler.MinMaxScaler
pub use ml.preprocessing.label_encoder.LabelEncoder
pub use ml.preprocessing.one_hot_encoder.OneHotEncoder
pub use ml.model_selection.split.train_test_split
pub use ml.model_selection.kfold.KFold
pub use ml.model_selection.stratified_kfold.StratifiedKFold
pub use ml.model_selection.cross_val.{ cross_val_score, ScoringFn }
pub use ml.pipeline.{ Pipeline2, Pipeline3, ColumnTransformer2, ColumnTransformerStep, RemainderPolicy }
pub use ml.linear.linear_regression.LinearRegression
pub use ml.linear.ridge.Ridge
pub use ml.linear.logistic_regression.LogisticRegression   # stub
pub use ml.linear.lasso.Lasso                              # stub
pub use ml.tree.decision_tree.{ DecisionTreeRegressor, DecisionTreeClassifier }  # stubs
pub use ml.cluster.kmeans.KMeans                           # stub
pub use ml.neighbors.knn.KNeighborsClassifier              # stub
pub use ml.metrics                                         # sub-namespace
```

Verify: `use std.ml` in a test file should resolve all public names without ambiguity. `use std.ml.metrics` resolves metric functions.

Run `bin/simple build lint` on the assembled module. Zero primitive-type leaks in any exported signature.

Spec: `test/ml/mod_spec.spl` — import `use std.ml`, reference one name from each major group (MlError, Estimator, StandardScaler, Pipeline2, LinearRegression, metrics.mse); verify compilation and basic construction without errors.

---

## Group 8: Integration and Acceptance Verification

### T-ML-17: End-to-end pipeline integration spec
**Phase:** v1.1
**Effort:** ≤1 day
**File:** `test/ml/pipeline_e2e_spec.spl`
**Deps:** T-ML-11 (Pipeline2), T-ML-03 (StandardScaler), T-ML-12 (LinearRegression), T-ML-07 (train_test_split), T-ML-15 (metrics)

Write a single spec file that exercises the canonical sklearn workflow in Simple:

1. Generate 50×2 synthetic NDArray<Float64> input (x) and NDArray<Float64> labels (y) using NDArray factory methods
2. `train_test_split(x, y, test_size=Float64(0.2), seed=Index(42))`
3. Construct `Pipeline2<StandardScaler, LinearRegression>`
4. `pipeline.fit(x_train, y_train)?`
5. `pipeline.predict(x_test)?`
6. `metrics.r2(y_test, y_pred)?` — assert result is Float64
7. `metrics.mse(y_test, y_pred)?` — assert result is Float64

Run with `SIMPLE_BLAS_BACKEND=mock`. The mock gesv must return a plausible solution for the spec to pass; if mock returns zeros, use a pre-solved fixture (known coefficients baked into y construction).

This spec is the v1.1 → v2 acceptance gate for the ml area.

---

### T-ML-18: AC-7 compliance sweep
**Phase:** v1.1
**Effort:** ≤1 day
**File:** No new files — verification pass only
**Deps:** T-ML-01 through T-ML-17

Run the complete ml spec suite:

```
SIMPLE_BLAS_BACKEND=mock bin/simple test src/lib/gc_async_mut/ml/
SIMPLE_BLAS_BACKEND=mock bin/simple test test/ml/
bin/simple build lint src/lib/gc_async_mut/ml/
```

Check:
- [ ] Zero `skip()` calls in any ml spec
- [ ] Zero TODO→NOTE conversions anywhere in ml source or specs
- [ ] Zero primitive types (`f64`, `i64`, `bool`, `str`) in any public function signature or exported struct field
- [ ] `nn/loss` and `nn/norm` are re-exported (grep for `pub use common.pure.nn`); no duplicate definition
- [ ] `DType` and `Device` not defined in ml/ — only re-exported
- [ ] cuML not referenced anywhere in ml/ source
- [ ] PERF-SUGAR-003 observation entry promoted from `anticipated` to `observed` or `fixed` in `doc/08_tracking/feature_request/scilib_perf_sugar.md`

If any item fails: do not ship, fix at root cause. No cover-up suppression.

---

## Dependency Graph Summary

```
T-ML-01 (types)
  └─ T-ML-02 (traits)
       ├─ T-ML-03 (StandardScaler)         ← T-NDARRAY-ops
       ├─ T-ML-04 (MinMaxScaler)           ← T-NDARRAY-ops
       ├─ T-ML-05 (LabelEncoder)           ← T-DF-Series
       ├─ T-ML-06 (OneHotEncoder)          ← T-ML-05
       ├─ T-ML-07 (train_test_split)       ← T-NDARRAY-ops
       ├─ T-ML-08 (KFold)                  ← T-NDARRAY-ops
       ├─ T-ML-09 (StratifiedKFold)        ← T-ML-08, T-ML-05
       ├─ T-ML-10 (cross_val_score)        ← T-ML-08, T-ML-15
       ├─ T-ML-11 (Pipeline2/3 + ColTrans) ← T-ML-03
       ├─ T-ML-12 (LinearRegression)       ← T-LAPACK-gesv
       ├─ T-ML-13 (Ridge)                  ← T-LAPACK-gesv
       ├─ T-ML-14 (stubs)
       └─ T-ML-15 (metrics)               ← T-NDARRAY-ops
T-ML-16 (mod.spl facade)                  ← T-ML-01..15
T-ML-17 (e2e spec)                        ← T-ML-11, T-ML-12, T-ML-07, T-ML-15
T-ML-18 (AC-7 sweep)                      ← T-ML-01..17
```

**Cross-area deps (explicit):**
- `T-DF-01..08` — DataFrame/Series/from_ndarray must be complete before T-ML-10 (cross_val DataLoader) and T-ML-05 (LabelEncoder uses Series-like NDArray<text> idiom)
- `T-NDARRAY-ops` — broadcasting, axis-parameterised mean/std, slicing must be complete before T-ML-03..10
- `T-NDARRAY-types` — Shape, Index, Float64, NDArray<Float64> wrappers before T-ML-01
- `T-LAPACK-gesv` — gesv and dgels before T-ML-12, T-ML-13
- `T-LAPACK-gesvd` — only needed if SVD-based LinearRegression variant is added (not in v1.1 scope; Ridge uses gesv)

**Parallel-safe pairs (disjoint files, may run simultaneously):**
- T-ML-03 and T-ML-04 (different files in preprocessing/)
- T-ML-07 and T-ML-08 (different files in model_selection/)
- T-ML-12 and T-ML-13 (different files in linear/)
- T-ML-14 stubs (all separate stub files)
- T-ML-15 (metrics.spl — fully independent of model files)

**Must be sequential:**
- T-ML-01 → T-ML-02 → all others (trait definitions must exist before implementors)
- T-ML-05 → T-ML-06 (OneHotEncoder builds on LabelEncoder category logic)
- T-ML-08 → T-ML-09 (StratifiedKFold extends KFold indexing)
- T-ML-15 → T-ML-10 (cross_val_score calls metrics)
- T-ML-16 → T-ML-17 → T-ML-18 (facade then integration then sweep)

---

## Risk Register (ml area)

| Risk | Task | Mitigation |
|------|------|-----------|
| Pipeline heterogeneous types: Simple lacks dyn dispatch and monomorphized generics in interpreter | T-ML-11 | Ship Pipeline2/Pipeline3 hand-specialized forms; document generic Pipeline<Steps> as v2 target; file compiler_requests.md entry |
| OneHotEncoder sparse output: no sparse matrix type in v1.1 NDArray | T-ML-06 | Dense output only; return MlError.InvalidInput for sparse_output=true; explicit v2 deferral |
| fit() workspace allocation (gesv, dgels): LAPACK workspace query pattern adds two FFI calls per fit | T-ML-12, T-ML-13 | Delegate entirely to T-LAPACK-gesv implementation; ml tasks do not re-implement workspace logic; cross-area dep is explicit |
| PERF-SUGAR-003 (generic NDArray<T> dispatch in interpreter): accuracy<T>, cross_val_score<E> may be unusably slow | T-ML-10, T-ML-15 | Observe and document in PERF-SUGAR-003 tracking entry; do not workaround with skip() or mode=native; proceed with interpreter mode |
| StratifiedKFold per-class groupby without std.df: local implementation needed | T-ML-09 | Implement local group_by_label using NDArray sort+scan only; keep disjoint from df area |
| cross_val_score clone semantics: Python clone() has no Simple equivalent | T-ML-10 | Factory-function pattern (fn() -> E); document as explicit design decision in file header |
| LabelEncoder NDArray<text>: generic text arrays may trigger PERF-SUGAR-003 | T-ML-05 | Same watchful approach; note observation if interpreter is slow |

---

## File Layout

```
src/lib/gc_async_mut/ml/
  types.spl                              # T-ML-01
  traits.spl                             # T-ML-02
  preprocessing/
    standard_scaler.spl                  # T-ML-03
    minmax_scaler.spl                    # T-ML-04
    label_encoder.spl                    # T-ML-05
    one_hot_encoder.spl                  # T-ML-06
  model_selection/
    split.spl                            # T-ML-07
    kfold.spl                            # T-ML-08
    stratified_kfold.spl                 # T-ML-09
    cross_val.spl                        # T-ML-10
  pipeline.spl                           # T-ML-11 (Pipeline2, Pipeline3, ColumnTransformer2)
  linear/
    linear_regression.spl                # T-ML-12
    ridge.spl                            # T-ML-13
    logistic_regression.spl              # T-ML-14 stub
    lasso.spl                            # T-ML-14 stub
  tree/
    decision_tree.spl                    # T-ML-14 stub
  cluster/
    kmeans.spl                           # T-ML-14 stub
  neighbors/
    knn.spl                              # T-ML-14 stub
  metrics.spl                            # T-ML-15
  mod.spl                                # T-ML-16

test/ml/
  types_spec.spl
  traits_spec.spl
  standard_scaler_spec.spl
  minmax_scaler_spec.spl
  label_encoder_spec.spl
  one_hot_encoder_spec.spl
  train_test_split_spec.spl
  kfold_spec.spl
  stratified_kfold_spec.spl
  cross_val_score_spec.spl
  pipeline_spec.spl
  column_transformer_spec.spl
  linear_regression_spec.spl
  ridge_spec.spl
  stubs_spec.spl
  metrics_spec.spl
  mod_spec.spl
  pipeline_e2e_spec.spl                  # T-ML-17
```
