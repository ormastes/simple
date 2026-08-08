# Python API Surface Inventory: NumPy / pandas / scikit-learn

**Phase:** 2-research · **Date:** 2026-04-27
**Flags:** `C`=collision with `src/lib/` · `M`=math-block-friendly · `P`=no-primitive pressure
**Overlap:** `Tensor`+factory in `nogc_sync_mut/src/tensor.spl`; `Table`/`Column` in `src/table.spl`. `Tensor→NDArray` rename is arch-phase decision.

---

## 1. NumPy (53 entries) → `std.ndarray` / `std.linalg`

### Constructors & DType

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `array` | `np.array(obj, dtype=None)` | medium | dtype dispatch; copy semantics | `from_seq<T>` | P |
| `zeros` | `np.zeros(shape, dtype)` | trivial | maps to `Tensor.zeros` | `zeros<T>` | C |
| `ones` | `np.ones(shape, dtype)` | trivial | same | `ones<T>` | C |
| `empty` | `np.empty(shape, dtype)` | trivial | uninit alloc | `empty<T>` | C |
| `full` | `np.full(shape, fill_value)` | trivial | scalar broadcast | `full<T>` | P |
| `arange` | `np.arange(start, stop, step)` | trivial | maps to `tensor/factory.arange` | `arange<T>` | C P |
| `linspace` | `np.linspace(start, stop, num)` | trivial | closed-form fill | `linspace` | C P |
| `eye` | `np.eye(N, M=None, k=0)` | trivial | closed-form | `eye` | — |
| `dtype` | `np.dtype(obj)` | medium | np.float64→`Float64`; no raw primitives | `DType` enum | P |

### Shape / Layout

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `shape` | `a.shape` | trivial | attribute; on `Tensor` | `ndarray.shape` | — |
| `reshape` | `a.reshape(newshape)` | medium | strides; no-copy contract | `ndarray.reshape` | C M |
| `transpose` | `a.transpose(*axes)` | medium | stride permutation; `Tensor.transpose` exists | `ndarray.transpose` | C M |
| `squeeze` | `a.squeeze(axis)` | trivial | size-1 axis removal | `ndarray.squeeze` | C |
| `flatten` | `a.flatten()` | trivial | row-major contiguous copy | `ndarray.flatten` | — |

### Indexing / Slicing

| Name | Description | Diff | Why | Simple Name | Flags |
|------|-------------|------|-----|-------------|-------|
| `a[i,j]` | Integer element access | medium | multi-axis; `Index` not int | `ndarray[i,j]` | M P |
| `a[1:4,::2]` | Stride-view slice | medium | stride arithmetic; math-block `a[lo..hi]` | `ndarray[range,...]` | M |
| `a[[0,2,4]]` | Integer-array gather | hard | gather kernel; no primitive array literal | `ndarray.gather` | P |
| `a[a>0]` | Boolean mask filter | hard | broadcast+ufunc result type | `ndarray.mask` | M |
| `np.where(cond,x,y)` | Conditional select | hard | broadcast-compat shapes + dtype unify | `where<T>` | M P |
| broadcasting | Shape alignment rules | hard | core engine; all ufuncs depend on it | `broadcast_shapes` | M |

### Ufuncs (elementwise)

| Name | Diff | Why | Simple Name | Flags |
|------|------|-----|-------------|-------|
| `add/sub/mul/div` | medium | broadcast+dtype dispatch; `+*-/` operators | `add/sub/mul/div<T>` | M |
| `exp/log` | medium | conflict `common/optimization/` and `common/complex/` | `ndarray.exp/log` | C M |
| `sin/cos/sqrt` | medium | conflict `common/complex/trigonometric.*` and `common/optimization/` | `ndarray.sin/cos/sqrt` | C M |

### Reductions

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `sum/mean` | `np.sum/mean(a, axis, ...)` | medium | axis dispatch; `Tensor.sum/mean` exist | `ndarray.sum/mean` | C M |
| `std` | `np.std(a, axis, ddof)` | medium | ddof param; `Tensor.std` exists | `ndarray.std` | C M |
| `min/max` | `np.min/max(a, axis)` | trivial | `Tensor.min/max` exist | `ndarray.min/max` | C |
| `argmax` | `np.argmax(a, axis)` | medium | returns `NDArray<Index>` | `ndarray.argmax` | P |
| `argsort` | `np.argsort(a, axis)` | hard | sort-permutation; no stable sort in stdlib yet | `ndarray.argsort` | P |

### Linear Algebra (`std.linalg`)

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `dot` | `np.dot(a, b)` | medium | 1-D dot or 2-D matmul (BLAS) | `linalg.dot<T>` | C M |
| `matmul` | `np.matmul(a, b)` | medium | strict 2-D+; `@` operator | `linalg.matmul<T>` | M |
| `inv` | `np.linalg.inv(a)` | hard | LAPACK DGETRI; singular error path | `linalg.inv` | — |
| `solve` | `np.linalg.solve(a, b)` | hard | LAPACK DGESV; hide pivot array | `linalg.solve` | — |
| `eig` | `np.linalg.eig(a)` | hard | LAPACK DGEEV; complex output→`Complex64` | `linalg.eig` | P |
| `svd` | `np.linalg.svd(a, full_matrices)` | hard | LAPACK DGESVD; three outputs | `linalg.svd` | — |
| `qr` | `np.linalg.qr(a, mode)` | hard | LAPACK DGEQRF+DORGQR; mode enum | `linalg.qr` | — |
| `cholesky` | `np.linalg.cholesky(a)` | hard | LAPACK DPOTRF; non-PD error | `linalg.cholesky` | — |
| `norm` | `np.linalg.norm(x, ord, axis)` | medium | ord dispatch; `Tensor.norm(p)` exists | `linalg.norm` | C |

### Random & I/O

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `default_rng` | `np.random.default_rng(seed)` | medium | mutable `RngState` wrapper | `random.default_rng` | P |
| `normal/uniform` | `rng.normal/uniform(loc,scale,size)` | medium | FFI to cuRAND or host | `rng.normal/uniform` | — |
| `integers` | `rng.integers(low,high,size)` | medium | `NDArray<Index>` return | `rng.integers` | P |
| `save/load` | `np.save/load(file, arr)` | medium | .npy header; no pickle | `io.save/load<T>` | — |
| `loadtxt` | `np.loadtxt(fname, dtype, delimiter)` | hard | string parse + dtype inference + delimiter dispatch | `io.load_txt<T>` | P |
| `genfromtxt` | `np.genfromtxt(fname, dtype, filling_values)` | hard | structured dtype + partial parse + fill logic | `io.gen_from_txt` | P |

---

## 2. pandas (48 entries) → `std.df`

`std.df` wraps and extends existing `Table`/`Column`.

### Core Types & Indexing

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `DataFrame` | `pd.DataFrame(data, index, columns)` | medium | dtype inference per column; polymorphic | `DataFrame.new` | P |
| `Series` | `pd.Series(data, index, name, dtype)` | medium | generic `Series<T>`; optional label index | `Series.new<T>` | P |
| `loc` | `df.loc[label, col]` | hard | label align; multi-axis; label-slice | `df.loc` | M P |
| `iloc` | `df.iloc[i, j]` | medium | integer positional | `df.iloc` | M P |
| `at` / `iat` | scalar label/integer access | trivial | single-cell fast path | `df.at` / `df.iat` | P |

### Column Operations

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `assign` | `df.assign(**kwargs)` | medium | variable-arity→named map | `df.assign` | P |
| `drop` | `df.drop(labels, axis)` | medium | axis dispatch; `Table.drop` exists | `df.drop` | C |
| `rename` | `df.rename(columns={})` | trivial | `Table.rename` exists | `df.rename` | C |
| `dtypes` | `df.dtypes` | trivial | `Series<DType>` attribute | `df.dtypes` | C |
| `astype` | `df.astype(dtype)` | medium | per-column cast | `df.astype` | P |
| `df['col']` | column subscript | trivial | single→`Series`; multi→`DataFrame` | `df[col]` | M |

### GroupBy

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `groupby` | `df.groupby(by, sort)` | hard | hash-aggregate; lazy; multi-key | `df.groupby` | — |
| `agg` | `gb.agg(func)` | hard | func polymorphic: name/callable/dict | `GroupBy.agg` | P |
| `sum/mean` (gb) | `gb.sum()` / `gb.mean()` | medium | groupby shorthand | `GroupBy.sum/mean` | C |
| `transform` | `gb.transform(func)` | hard | output shape==input; scatter | `GroupBy.transform` | M P |

### Merge / Join / Concat

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `merge` | `pd.merge(left,right,how,on)` | hard | hash+sort-merge; how/multi-key | `std.df.merge` | P |
| `concat` | `pd.concat(objs, axis, ignore_index)` | medium | row/col stack; dtype unify | `std.df.concat` | — |
| `join` | `df.join(other, on, how)` | hard | index-aligned join | `df.join` | — |

### Missing Values

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `isna` | `df.isna()` | trivial | bool frame/series | `df.is_na` | M |
| `fillna` | `df.fillna(value)` | medium | scalar/dict/forward-fill | `df.fill_na` | P |
| `dropna` | `df.dropna(axis, how)` | medium | how=any/all; axis | `df.drop_na` | — |

### I/O & Datetime

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `read_csv` | `pd.read_csv(filepath, sep, header, dtype)` | hard | dtype inference; nullable; header | `io.read_csv` | P |
| `to_csv` | `df.to_csv(path, sep, index)` | medium | nullable+escape | `df.to_csv` | — |
| `read_parquet` | `pd.read_parquet(path, columns)` | hard | binary; Parquet FFI | `io.read_parquet` | — |
| `read_json` | `pd.read_json(path, orient)` | medium | orient dispatch; recursive | `io.read_json` | P |
| `to_datetime` | `pd.to_datetime(arg, format, utc)` | hard | format auto-detect; tz; polymorphic | `to_datetime` | P |
| `dt` accessor | `s.dt.year/.month/.day_of_week` | medium | accessor; many sub-fields | `Series<DateTime>.dt` | — |

### Inspection & Sorting

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `head/tail` | `df.head/tail(n=5)` | trivial | `Table.head/tail` exist | `df.head/tail` | C |
| `describe` | `df.describe(include)` | medium | per-column stats+quartiles | `df.describe` | — |
| `info` | `df.info(verbose)` | trivial | introspection text | `df.info` | — |
| `sort_values` | `df.sort_values(by, ascending, na_position)` | medium | multi-key stable sort; NaN pos | `df.sort_values` | P |
| `sort_index` | `df.sort_index(axis, ascending)` | medium | index sort; axis dispatch | `df.sort_index` | — |
| `set_index` | `df.set_index(keys, drop)` | medium | promote column→label index | `df.set_index` | P |
| `reset_index` | `df.reset_index(drop)` | medium | inverse set_index | `df.reset_index` | — |

### Apply / Element-wise / Reshape / Window

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `apply` | `df.apply(func, axis)` | hard | axis dispatch; return shape varies; closure param | `df.apply` | P |
| `map` | `s.map(func_or_dict)` | medium | `Column.map<U>` exists; dict lookup path | `series.map<U>` | C |
| `value_counts/unique/nunique` | `s.value_counts/unique/nunique()` | trivial/medium | `Column.value_counts/unique` exist | `series.value_counts/unique/nunique` | C |
| `drop_duplicates` | `df.drop_duplicates(subset, keep)` | medium | hash rows; subset+keep | `df.drop_duplicates` | — |
| `pivot_table` | `df.pivot_table(values,index,columns,aggfunc)` | hard | multi-level groupby+reshape; aggfunc polymorphic | `df.pivot_table` | P |
| `melt` | `pd.melt(df, id_vars, value_vars)` | medium | wide→long reshape | `std.df.melt` | — |
| `str` accessor | `s.str.lower()/.contains()/.split()` | medium | vectorized text ops; `std.common.text` | `Series<text>.str` | — |
| `rolling` | `df.rolling(window, min_periods)` | hard | lazy window; ring-buffer state | `df.rolling` | — |
| `plot` | `df.plot(kind, x, y)` | hard | deferred; `std.ui` dep; v1 stub | `df.plot` (stub) | — |

---

## 3. scikit-learn (28 entries) → `std.ml`

### Estimator Interface (trait) & Composition

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `fit` | `est.fit(X, y=None)` | medium | trait; typed `NDArray<Float64>` input | `Estimator.fit` | — |
| `predict` | `est.predict(X)` | medium | return type varies by model | `Estimator.predict` | — |
| `transform` | `est.transform(X)` | medium | output shape may differ from input | `Transformer.transform` | — |
| `fit_transform` | `est.fit_transform(X, y)` | medium | fit+transform; overridable default | `Transformer.fit_transform` | — |
| `score` | `est.score(X, y)` | medium | `Float64`; model-dependent metric | `Estimator.score` | — |
| `Pipeline` | `Pipeline(steps)` | hard | heterogeneous steps; clone semantics; no inheritance | `ml.Pipeline.new` | P |
| `ColumnTransformer` | `ColumnTransformer(transformers,remainder)` | hard | per-column-subset dispatch; dtype-aware routing | `ml.ColumnTransformer.new` | P |

### Model Selection

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `train_test_split` | `train_test_split(*arrays, test_size, seed)` | medium | variadic arrays; random shuffle | `ml.train_test_split<T>` | P |
| `cross_val_score` | `cross_val_score(est, X, y, cv, scoring)` | hard | clone per fold; scoring polymorphic | `ml.cross_val_score` | P |
| `KFold` | `KFold(n_splits, shuffle, seed)` | medium | index-pair iterator | `ml.KFold.new` | P |
| `StratifiedKFold` | `StratifiedKFold(n_splits, shuffle)` | hard | label-freq equalization; sort+count | `ml.StratifiedKFold.new` | P |

### Preprocessing

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `StandardScaler` | `StandardScaler(with_mean, with_std)` | medium | stateful mean/std per feature | `ml.StandardScaler.new` | — |
| `MinMaxScaler` | `MinMaxScaler(feature_range=(0,1))` | medium | stateful min/max per feature | `ml.MinMaxScaler.new` | — |
| `OneHotEncoder` | `OneHotEncoder(sparse_output, handle_unknown)` | hard | sparse output; unknown-category state | `ml.OneHotEncoder.new` | P |
| `LabelEncoder` | `LabelEncoder()` | medium | sorted labels→`Index`; inverse_transform needed | `ml.LabelEncoder.new` | P |

### Models

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `LinearRegression` | `LinearRegression(fit_intercept)` | medium | LAPACK DGELS / normal equation | `ml.LinearRegression.new` | — |
| `LogisticRegression` | `LogisticRegression(C, max_iter, solver)` | hard | iterative L-BFGS/SGD; multi-class; convergence | `ml.LogisticRegression.new` | P |
| `Ridge` | `Ridge(alpha, fit_intercept)` | medium | closed-form `(XᵀX+αI)⁻¹Xᵀy` | `ml.Ridge.new` | M |
| `Lasso` | `Lasso(alpha, max_iter, tol)` | hard | coordinate descent; convergence | `ml.Lasso.new` | P |
| `DecisionTreeRegressor` | `DecisionTreeRegressor(max_depth, min_split)` | hard | recursive split + variance reduction | `ml.DecisionTreeRegressor.new` | P |
| `DecisionTreeClassifier` | `DecisionTreeClassifier(max_depth, criterion)` | hard | Gini/entropy criterion dispatch | `ml.DecisionTreeClassifier.new` | P |
| `KMeans` | `KMeans(n_clusters, max_iter, random_state)` | hard | Lloyd iteration; mutable RNG state | `ml.KMeans.new` | P |
| `KNeighborsClassifier` | `KNeighborsClassifier(n_neighbors, algorithm)` | hard | brute/KD-tree; distance + majority vote | `ml.KNeighborsClassifier.new` | P |

### Metrics

| Name | Python Signature | Diff | Why | Simple Name | Flags |
|------|-----------------|------|-----|-------------|-------|
| `mean_squared_error` | `mse(y_true, y_pred, squared)` | trivial | reduction | `metrics.mse` | M |
| `accuracy_score` | `accuracy(y_true, y_pred, normalize)` | trivial | count equality | `metrics.accuracy<T>` | — |
| `r2_score` | `r2(y_true, y_pred)` | trivial | reduction | `metrics.r2` | M |
| `confusion_matrix` | `confusion_matrix(y_true, y_pred, labels, normalize)` | hard | label enum + normalization dispatch | `metrics.confusion_matrix<T>` | P |
| `classification_report` | `classification_report(y_true, y_pred, target_names)` | hard | per-class P/R/F1; text output | `metrics.classification_report<T>` | P |

---

## Collision Index

> `mean/std/sum/norm/transpose/reshape/squeeze` are `Tensor` methods, not `std.math` free functions — resolved by keeping as `NDArray<T>` methods. Free-function collisions below are the risky ones.

| Name | Existing location | Resolution |
|------|------------------|-----------|
| `sin/cos/tan` | `common/complex/trigonometric.spl`, `common/optimization/` | qualify `std.ndarray.*` vs `std.math.*` |
| `exp/log/sqrt` | `common/complex/exponential.spl`, `common/optimization/utilities.spl` | same |
| `min/max/abs` | `common/ascii_art/`, `common/optimization/`, `common/color/` | NDArray methods; no free-fn clash at `std.ndarray` level |
| `floor` | `common/avl_tree/search.spl` | unrelated semantics; safe |
| `zeros/ones/empty/arange/linspace` | `tensor/factory.spl` | `std.ndarray.*` wraps/shadows; arch-phase decision |

**Total: 15 distinct collision names**

---

## Summary

| Library | Entries | Hard |
|---------|---------|------|
| NumPy (`std.ndarray`+`std.linalg`) | 53 | 11 |
| pandas (`std.df`) | 48 | 11 |
| scikit-learn (`std.ml`) | 28 | 11 |
| **Total** | **129** | **33** |
