# scilib-port: std.df TODO — DataFrame (v1.1)

**Phase:** v1.1 (starts after v1 acceptance gates green: PERF-SUGAR-001 fixed, ndarray specs pass)  
**Location:** `src/lib/nogc_sync_mut/df/`  
**Import:** `use std.df`  
**Tier:** `nogc_sync_mut/` — synchronous I/O, FFI, mutable state; no GC required  

**Hard constraints (apply to every task):**
- No primitive types in any public signature — `Float64`, `Int64`, `Index`, `Bool`, `Symbol`, `text`; never `f64`/`i64`/`bool`/`str`
- No inheritance — composition and traits only
- DataFrame ops are PLAIN method calls — NEVER inside `math{}` (architect anti-pattern #2; string-keyed indexing is fundamentally incompatible with `MathExpr`)
- All specs run via `bin/simple test` in interpreter mode with zero `skip()`; no `--mode=native` bypass (AC-7)
- `sum`/`mean`/`min`/`max` are methods on `DataFrame`/`Series<T>`, never free functions (naming-harmony rule)
- Compose `std.common.csv` for CSV I/O — do not reimplement
- Compose `std.common.statistics.descriptive` for `describe()` — do not reimplement

**Deps on sibling areas (must be green before df impl begins):**
- T-NDARRAY-NN: `NDArray<T>`, `Shape`, `Index`, `Float64`, `Int64`, `Bool` wrappers in place; `StorageBackend` trait implemented
- T-NDARRAY-NN: `NDArray<Bool>` for boolean mask ops
- T-NDARRAY-NN: Strided view / PERF-SUGAR-005 status = `fixed` (required for column ops without O(n) copy)
- T-PERFSUGAR-NN: PERF-SUGAR-006 (`rt_intern_symbol`) either fixed or formal fallback (`Symbol = text`) documented

---

## Task List

### Phase A — Pre-implementation gate (prerequisite checks)

**T-DF-01** — Verify PERF-SUGAR-005 strided-view status  
Phase: v1.1 gate check  
Dep: T-NDARRAY-NN (strided view impl)  
Action: Confirm `NDArray<T>` strided views are O(1) and return non-owning view. If PERF-SUGAR-005 is not `fixed`, document a concrete workaround (column ops copy at construction time with a `#[perf: copy-on-column-access]` annotation) and file the deferral. Do NOT proceed to T-DF-04 without either status=fixed or a documented fallback.  
Deliverable: Entry in `scilib_perf_sugar.md` updated to `fixed` or `deferred-with-plan`.  
Estimate: 0.5 day

**T-DF-02** — Verify or implement PERF-SUGAR-006 Symbol intern  
Phase: v1.1 gate check  
Dep: none (compiler-level concern)  
Action: Check whether `rt_intern_symbol(str: text) -> i64` is available. If not, implement `Symbol = text` fallback (O(len) equality). Update `scilib_perf_sugar.md` with observed status and fallback plan. This decision gates T-DF-05 (type definitions).  
Deliverable: PERF-SUGAR-006 entry updated; fallback decision recorded.  
Estimate: 0.5 day

**T-DF-03** — Observe PERF-SUGAR-007 lazy-groupby risk  
Phase: v1.1 gate check  
Dep: T-DF-01 (strided view status)  
Action: Confirm the `RowRange`-based lazy groupby design (no group materialization) is viable with the strided-view result from T-DF-01. If PERF-SUGAR-005 is deferred (copy fallback), document that groupby will be O(n) copy per group in v1.1 and file a concrete follow-up in `scilib_perf_sugar.md` under PERF-SUGAR-007.  
Deliverable: PERF-SUGAR-007 status updated.  
Estimate: 0.25 day

---

### Phase B — Core types and specs (write specs first, then impl)

**T-DF-04** — Spec: `Series<T>` construction and field access  
Phase: v1.1  
Dep: T-DF-02 (Symbol decision)  
Action: Write `src/lib/nogc_sync_mut/df/spec/series_construct_spec.spl`. Assertions: `Series.new<Float64>(name, data, index)` returns correct `.name`, `.len()`, `.dtype`. Test `Series<text>`, `Series<Int64>`, `Series<Bool>`. No `skip()`. No primitive leak.  
Deliverable: Spec file; all assertions concrete.  
Estimate: 0.5 day

**T-DF-05** — Impl: `Series<T>`, `DataFrame`, `SeriesErased`, `Symbol` types  
Phase: v1.1  
Dep: T-DF-02, T-DF-04 (spec must exist before impl)  
Action: Implement `src/lib/nogc_sync_mut/df/types.spl`. Fields (per arch §8):
- `Series<T>`: `_name: Symbol`, `_data: NDArray<T>`, `_index: NDArray<Index>`
- `DataFrame`: `_schema: [Symbol]`, `_cols: [SeriesErased]`, `_index: NDArray<Index>`
- `SeriesErased` enum: `F64Series(Series<Float64>)`, `I64Series(Series<Int64>)`, `TextSeries(Series<text>)`, `BoolSeries(Series<Bool>)`
- `Symbol`: `rt_intern_symbol`-backed if PERF-SUGAR-006 fixed; else `Symbol = text` alias  
No inheritance. All fields private. Public accessor methods only.  
Deliverable: `types.spl`; `bin/simple test` on T-DF-04 spec passes.  
Estimate: 1.5 days

**T-DF-06** — Spec: `DataFrame` construction from sequences  
Phase: v1.1  
Dep: T-DF-05  
Action: Write `spec/dataframe_construct_spec.spl`. Assertions: `DataFrame.from_cols(cols: [SeriesErased]) -> DataFrame` produces correct `.schema()`, `.num_rows()`, `.num_cols()`. Test mismatched-length error path returns `Result.Err`.  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-07** — Impl: `DataFrame.from_cols`, `DataFrame.from_ndarray`  
Phase: v1.1  
Dep: T-DF-05, T-DF-06  
Action: Implement in `src/lib/nogc_sync_mut/df/construct.spl`:
- `fn DataFrame.from_cols(cols: [SeriesErased]) -> Result<DataFrame, DfError>`
- `fn DataFrame.from_ndarray(arr: NDArray<Float64>, cols: [Symbol]) -> Result<DataFrame, DfError>`
- `DfError` enum: `ShapeMismatch`, `ColumnNotFound(Symbol)`, `DTypeMismatch(DType, DType)`, `IoError(text)` — defined in `types.spl`  
Deliverable: `construct.spl`; T-DF-06 spec passes.  
Estimate: 1 day

---

### Phase C — Indexing (loc / iloc / at / iat)

**T-DF-08** — Spec: column select and multi-column select  
Phase: v1.1  
Dep: T-DF-07  
Action: Write `spec/indexing_spec.spl`. Assertions:
- `df[col: Symbol] -> SeriesErased` returns correct series
- `df.select(cols: [Symbol]) -> DataFrame` returns sub-frame with correct schema
- Unknown column returns `Result.Err(ColumnNotFound)`  
No `skip()`.  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-09** — Impl: `df[col]`, `df.select`, `df.iloc`, `df.loc`, `df.at`, `df.iat`  
Phase: v1.1  
Dep: T-DF-07, T-DF-08  
Action: Implement in `src/lib/nogc_sync_mut/df/ops.spl`:
- `fn DataFrame.col(name: Symbol) -> Result<SeriesErased, DfError>` (subscript sugar via `[]`)
- `fn DataFrame.select(cols: [Symbol]) -> Result<DataFrame, DfError>`
- `fn DataFrame.iloc(row: Index, col: Index) -> Result<Value, DfError>` — positional scalar
- `fn DataFrame.loc(row: Index, col: Symbol) -> Result<Value, DfError>` — label scalar
- `fn DataFrame.at(row: Index, col: Symbol) -> Result<Value, DfError>` — single-cell fast path
- `fn DataFrame.iat(row: Index, col: Index) -> Result<Value, DfError>` — single-cell integer fast path
`Value` is a local enum `DfValue { F64(Float64), I64(Int64), Txt(text), B(Bool), Na }` defined in `types.spl`.  
Deliverable: `ops.spl` indexing section; T-DF-08 spec passes.  
Estimate: 1.5 days

---

### Phase D — Boolean filter and row range

**T-DF-10** — Spec: `df.filter` with boolean mask  
Phase: v1.1  
Dep: T-DF-09, T-NDARRAY-NN (NDArray<Bool>)  
Action: Write `spec/filter_spec.spl`. Assertions: `df.filter(mask: NDArray<Bool>) -> DataFrame` returns frame with only rows where mask is true; output `.num_rows()` matches `mask.sum()`; error on mask length mismatch.  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-11** — Impl: `df.filter`  
Phase: v1.1  
Dep: T-DF-09, T-DF-10  
Action: Implement `fn DataFrame.filter(mask: NDArray<Bool>) -> Result<DataFrame, DfError>` in `ops.spl`. Apply mask to each column using `NDArray` indexed gather (uses strided view or copy fallback per T-DF-01 decision). Return `Result.Err(ShapeMismatch)` if mask length != `num_rows`.  
Deliverable: Filter impl; T-DF-10 spec passes.  
Estimate: 1 day

---

### Phase E — Column operations (assign / drop / rename / dtypes / astype)

**T-DF-12** — Spec: column mutation ops  
Phase: v1.1  
Dep: T-DF-09  
Action: Write `spec/column_ops_spec.spl`. Assertions:
- `df.assign(name: Symbol, col: SeriesErased) -> DataFrame` adds or replaces column; schema updated
- `df.drop(col: Symbol) -> Result<DataFrame, DfError>` removes column; error if not found
- `df.rename(old: Symbol, new: Symbol) -> Result<DataFrame, DfError>` renames; schema updated
- `df.dtypes() -> Series<DType>` returns per-column dtype; names match schema
- `df.astype(col: Symbol, dtype: DType) -> Result<DataFrame, DfError>` recasts column  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-13** — Impl: `assign`, `drop`, `rename`, `dtypes`, `astype`  
Phase: v1.1  
Dep: T-DF-07, T-DF-12  
Action: Implement in `ops.spl`:
- `fn DataFrame.assign(name: Symbol, col: SeriesErased) -> DataFrame` — creates new DataFrame (immutable pattern; no in-place mutation at public API)
- `fn DataFrame.drop(col: Symbol) -> Result<DataFrame, DfError>`
- `fn DataFrame.rename(old: Symbol, new: Symbol) -> Result<DataFrame, DfError>`
- `fn DataFrame.dtypes() -> Series<DType>` — returns `Series<DType>` (typed, no primitives)
- `fn DataFrame.astype(col: Symbol, dtype: DType) -> Result<DataFrame, DfError>` — element-cast via `NDArray` dtype dispatch  
Deliverable: T-DF-12 spec passes.  
Estimate: 1.5 days

---

### Phase F — Scalar broadcast ops on Series<T>

**T-DF-14** — Spec: scalar broadcast on `Series<T>`  
Phase: v1.1  
Dep: T-DF-05  
Action: Write `spec/series_scalar_spec.spl`. Assertions:
- `s.add_scalar(rhs: Float64) -> Series<Float64>` — each element increased
- `s.mul_scalar(rhs: Float64) -> Series<Float64>` — each element scaled
- `s.sub_scalar`, `s.div_scalar` analogues
- Operator overloading `s + Float64(2.0)` calls `add_scalar` (verify via method dispatch, not free fn)  
**Risk:** This is the "broadcast scalar→Series" task. The risk is that operator overloading dispatch on a generic `Series<T>` with a non-Series RHS may not work in interpreter mode (PERF-SUGAR-003). If dispatch fails, implement as explicit `.add_scalar()` methods only (no operator sugar), and file a concrete PERF-SUGAR entry.  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-15** — Impl: `Series<T>` scalar broadcast methods  
Phase: v1.1  
Dep: T-DF-05, T-DF-14  
Action: Implement in `src/lib/nogc_sync_mut/df/series_ops.spl`:
- `fn Series<Float64>.add_scalar(rhs: Float64) -> Series<Float64>`
- `fn Series<Float64>.sub_scalar(rhs: Float64) -> Series<Float64>`
- `fn Series<Float64>.mul_scalar(rhs: Float64) -> Series<Float64>`
- `fn Series<Float64>.div_scalar(rhs: Float64) -> Series<Float64>`
- Same quartet for `Series<Int64>`
Each delegates to `_data.add_scalar(rhs)` on the underlying `NDArray<T>` (backed by `NDArray` elementwise ops from T-NDARRAY-NN).  
If PERF-SUGAR-003 blocks operator overload sugar: implement methods only; annotate with `# TODO(PERF-SUGAR-003): operator sugar pending generic dispatch fix`.  
Deliverable: `series_ops.spl`; T-DF-14 spec passes.  
Estimate: 1 day

---

### Phase G — Missing value handling (isna / fillna / dropna)

**T-DF-16** — Spec: missing value ops  
Phase: v1.1  
Dep: T-DF-09, T-DF-11  
Action: Write `spec/missing_spec.spl`. Assertions:
- `df.is_na() -> DataFrame` (bool frame — each column becomes `Series<Bool>`)
- `series.is_na() -> Series<Bool>`
- `df.fill_na(value: DfValue) -> DataFrame` — scalar fill
- `df.fill_na_col(col: Symbol, value: DfValue) -> Result<DataFrame, DfError>` — per-column fill
- `df.drop_na(how: NaHow) -> DataFrame` where `NaHow` enum: `Any`, `All` — drops rows  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-17** — Impl: `is_na`, `fill_na`, `drop_na` + `NaHow` enum  
Phase: v1.1  
Dep: T-DF-09, T-DF-16  
Action: Implement in `ops.spl`. NA representation: a companion `NDArray<Bool>` mask per `SeriesErased` column stored in `_na_mask` field (add to `Series<T>` in `types.spl`). `is_na()` returns the mask as a bool Series/DataFrame. `fill_na` substitutes masked elements. `drop_na(Any)` drops rows where any column has `_na_mask[row] = true`. `drop_na(All)` drops only rows where all columns are masked.  
Deliverable: NA mask field added to `types.spl`; T-DF-16 spec passes.  
Estimate: 1.5 days

---

### Phase H — Sorting and inspection

**T-DF-18** — Spec: `sort_values`, `head`, `tail`, `describe`, `info`  
Phase: v1.1  
Dep: T-DF-09  
Action: Write `spec/inspect_sort_spec.spl`. Assertions:
- `df.sort_values(by: Symbol, ascending: Bool) -> Result<DataFrame, DfError>` — sorted copy, NaN last
- `df.head(n: Index) -> DataFrame` — first n rows
- `df.tail(n: Index) -> DataFrame` — last n rows
- `df.describe() -> DataFrame` — numeric columns only; rows: count/mean/std/min/25%/50%/75%/max (delegates to `std.common.statistics.descriptive`)
- `df.info() -> text` — schema + dtypes + non-null counts  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-19** — Impl: `sort_values`, `head`, `tail`, `describe`, `info`  
Phase: v1.1  
Dep: T-DF-17, T-DF-18  
Action: Implement in `ops.spl`. `sort_values`: compute `argsort` via `NDArray.argsort` on the key column (delegates to T-NDARRAY-NN); reindex all columns with the sort permutation index. `head`/`tail`: slice `_index` and all columns via `NDArray` range. `describe`: extract numeric columns, delegate per-column stats to `std.common.statistics.descriptive.describe_vec`. `info`: build text summary (no primitives in return; `text` return type is allowed).  
Deliverable: T-DF-18 spec passes.  
Estimate: 1.5 days

---

### Phase I — Groupby (lazy RowRange engine)

**T-DF-20** — Spec: `groupby` lazy RowRange path  
Phase: v1.1  
Dep: T-DF-09, T-DF-11, T-DF-03 (PERF-SUGAR-007 observed)  
**High-risk task.** See risk note below.  
Action: Write `spec/groupby_spec.spl`. Assertions:
- `df.groupby(col: Symbol) -> GroupBy` — returns `GroupBy` handle (no materialization yet)
- `gb.sum() -> DataFrame` — result has one row per unique key, correct aggregated values
- `gb.mean() -> DataFrame` — same
- `gb.agg(f: fn(NDArray<Float64>) -> Float64) -> DataFrame` — user-supplied aggregator
- Test with 3-group frame; verify no group rows appear in output  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-21** — Impl: `DataFrame.groupby`, `GroupBy`, `RowRange`  
Phase: v1.1  
Dep: T-DF-07, T-DF-20  
**High-risk task.** Risk: hash-aggregate engine over `NDArray` column views requires: (a) sort-then-range strategy to avoid hash-map allocation (uses `NDArray.argsort` on key column — dep on T-NDARRAY-NN argsort), (b) strided column views per RowRange (PERF-SUGAR-005; copy fallback adds O(group_size) cost per group), (c) generic `agg` closure parameter — PERF-SUGAR-003 may prevent generic fn dispatch in interpreter mode.  
Mitigation: If PERF-SUGAR-003 blocks `agg(f: fn(...) -> Float64)`, ship `sum`/`mean` as hand-specialized methods only in v1.1; generic `agg` becomes v2 with a concrete PERF-SUGAR-003 tracking entry.  
Action: Implement `src/lib/nogc_sync_mut/df/groupby.spl`:
```
struct RowRange:
    key:   DfValue
    start: Index
    stop:  Index

struct GroupBy:
    _df:      DataFrame
    _col:     Symbol
    _ranges:  [RowRange]   # computed lazily on first iteration

fn DataFrame.groupby(col: Symbol) -> Result<GroupBy, DfError>
fn GroupBy.sum() -> DataFrame
fn GroupBy.mean() -> DataFrame
fn GroupBy.agg(f: fn(NDArray<Float64>) -> Float64) -> DataFrame  # may be deferred
```
Sort key column via `NDArray.argsort`, compute `RowRange` list from run-length encoding of sorted key. Each aggregation iterates `RowRange` and applies to column view.  
Deliverable: `groupby.spl`; T-DF-20 spec passes (or `agg` deferred with tracking entry).  
Estimate: 2 days

---

### Phase J — Merge / join / concat

**T-DF-22** — Spec: `concat` (row and column stacking)  
Phase: v1.1  
Dep: T-DF-07  
Action: Write `spec/concat_spec.spl`. Assertions:
- `std.df.concat(frames: [DataFrame], axis: ConcatAxis) -> Result<DataFrame, DfError>` where `ConcatAxis` enum: `Rows`, `Cols`
- Row concat: schema must match; output row count = sum of row counts
- Col concat: row count must match; output schema = union  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-23** — Impl: `concat`  
Phase: v1.1  
Dep: T-DF-07, T-DF-22  
Action: Implement `fn concat(frames: [DataFrame], axis: ConcatAxis) -> Result<DataFrame, DfError>` in `src/lib/nogc_sync_mut/df/ops.spl`. Row concat uses `NDArray.concat` on each column's backing `_data`. Col concat appends to `_schema` and `_cols`.  
Deliverable: T-DF-22 spec passes.  
Estimate: 1 day

**T-DF-24** — Spec: `merge` (inner/left join on key column)  
Phase: v1.1  
Dep: T-DF-21 (sort infrastructure)  
Action: Write `spec/merge_spec.spl`. Assertions:
- `std.df.merge(left: DataFrame, right: DataFrame, on: Symbol, how: JoinHow) -> Result<DataFrame, DfError>` where `JoinHow` enum: `Inner`, `Left`, `Right`, `Outer`
- Inner: only matching rows from both
- Left: all left rows; right NaN-filled where no match
- Right/Outer: analogous  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-25** — Impl: `merge` (sort-merge join strategy)  
Phase: v1.1  
Dep: T-DF-21, T-DF-24  
Action: Implement sort-merge join in `src/lib/nogc_sync_mut/df/merge.spl`. Sort both frames on `on` column (reuse argsort from T-DF-19). Two-pointer merge. Build output index arrays, then gather rows from both frames via `NDArray.gather`. Fill NA mask for unmatched rows in Left/Right/Outer.  
Deliverable: `merge.spl`; T-DF-24 spec passes.  
Estimate: 2 days

**T-DF-26** — Spec + Impl: `df.join`  
Phase: v1.1  
Dep: T-DF-25  
Action: Write `spec/join_spec.spl`. `df.join(other: DataFrame, on: Symbol, how: JoinHow) -> Result<DataFrame, DfError>` is a thin method wrapper over `merge`. Spec: join two frames; verify index alignment. Impl: delegate to `merge`. Combined spec+impl because `join` is a one-liner wrapper.  
Deliverable: Spec + impl; spec passes.  
Estimate: 0.5 day

---

### Phase K — I/O (read_csv / to_csv / read_parquet stub)

**T-DF-27** — Spec: `DataFrame.from_csv`  
Phase: v1.1  
Dep: T-DF-07  
**High-risk task.** See risk note below.  
Action: Write `spec/csv_spec.spl`. Assertions:
- `io.read_csv(path: text, sep: text, header: Bool) -> Result<DataFrame, DfError>` — composes `std.common.csv.parse`
- Correct schema inferred from header row
- Numeric columns become `Series<Float64>` or `Series<Int64>` (dtype inference — see T-DF-28)
- Non-numeric columns become `Series<text>`
- Rows with parse errors → NA (not hard failure)  
Deliverable: Spec file.  
Estimate: 0.5 day

**T-DF-28** — Impl: dtype inference engine for CSV  
Phase: v1.1  
Dep: T-DF-17, T-DF-27  
**High-risk task.** Risk: dtype inference (auto-detecting Float64 vs Int64 vs text per column) requires scanning the first `n` rows of each column, attempting typed parse, then deciding. Edge cases: mixed int/float columns, nullable columns, columns that look numeric but have "N/A"/"nan"/empty strings. Wrong inference produces silent data corruption.  
Strategy: Two-pass inference — pass 1 tries `Int64` parse; if any cell fails, try `Float64` parse; if any cell fails, use `text`. NA strings ("", "N/A", "nan", "NaN", "null") always set `_na_mask` rather than failing parse.  
Implement in `src/lib/nogc_sync_mut/df/io.spl`:
- `fn infer_dtype(cells: [text]) -> DType` — internal, not exported
- `fn read_csv(path: text, sep: text, header: Bool) -> Result<DataFrame, DfError>` — composes `std.common.csv.parse` for raw cell grid, then applies `infer_dtype` per column  
Deliverable: `io.spl` with `read_csv`; T-DF-27 spec passes.  
Estimate: 1.5 days

**T-DF-29** — Spec + Impl: `df.to_csv`  
Phase: v1.1  
Dep: T-DF-27  
Action: Write `spec/to_csv_spec.spl`. `fn DataFrame.to_csv(path: text, sep: text) -> Result<Unit, DfError>`. Spec: round-trip a simple frame through `to_csv` then `read_csv`; values match. Impl: composes `std.common.csv.serialize`. NA values written as empty string. Combined spec+impl (to_csv is straightforward).  
Deliverable: Spec + impl; spec passes.  
Estimate: 1 day

**T-DF-30** — Stub: `read_parquet` (deferred v2)  
Phase: v1.1 stub only  
Dep: T-DF-07  
Action: Add `fn read_parquet(path: text, cols: Option<[Symbol]>) -> Result<DataFrame, DfError>` that always returns `Result.Err(DfError.IoError("read_parquet: deferred to v2 (requires libparquet FFI)"))`. File a concrete feature request in `doc/08_tracking/feature_request/compiler_requests.md` — entry: "T-DF-30: read_parquet FFI: requires stable libparquet extern C surface; deferred from v1.1." No spec needed for a stub that always errors.  
Deliverable: Stub fn in `io.spl`; feature request entry.  
Estimate: 0.25 day

---

### Phase L — Apply / map / value_counts

**T-DF-31** — Spec + Impl: `Series<T>.map<U>`  
Phase: v1.1  
Dep: T-DF-05  
Action: Write `spec/series_map_spec.spl`. `fn Series<T>.map<U>(f: fn(T) -> U) -> Series<U>`. Composes over existing `std.common` `Column.map<U>` if available; else implements as `NDArray` element-wise loop. PERF-SUGAR-003 risk: generic `<U>` dispatch may be slow in interpreter. If so, ship concrete overloads (`map_float64`, `map_int64`, `map_text`) and file PERF-SUGAR entry.  
Deliverable: Spec + impl; spec passes.  
Estimate: 1 day

**T-DF-32** — Spec + Impl: `Series<T>.value_counts`, `unique`, `nunique`  
Phase: v1.1  
Dep: T-DF-05  
Action: Write `spec/series_counts_spec.spl`. Assertions:
- `s.value_counts() -> DataFrame` — two-column frame: values + counts; sorted descending by count
- `s.unique() -> Series<T>` — deduplicated values in order of first appearance
- `s.nunique() -> Index` — count of distinct values  
Implement using sort-then-run-length-encode (no hash map; avoids alloc pressure).  
Deliverable: Spec + impl; spec passes.  
Estimate: 1 day

**T-DF-33** — Spec + Impl: `df.apply`  
Phase: v1.1  
Dep: T-DF-05, T-DF-31  
Action: Write `spec/apply_spec.spl`. `fn DataFrame.apply(f: fn(SeriesErased) -> SeriesErased, axis: ApplyAxis) -> DataFrame` where `ApplyAxis` enum: `Cols`, `Rows`. Column-wise (`Cols`): applies `f` to each column, returns frame. Row-wise (`Rows`): constructs a single-row DataFrame per row — high alloc cost; document in spec as "use column-wise apply for perf". PERF-SUGAR-003 risk on `fn(SeriesErased)` dispatch; same deferral plan as T-DF-31.  
Deliverable: Spec + impl; spec passes.  
Estimate: 1 day

---

### Phase M — String accessor, drop_duplicates, set_index / reset_index

**T-DF-34** — Spec + Impl: `Series<text>.str` accessor  
Phase: v1.1  
Dep: T-DF-05  
Action: Write `spec/str_accessor_spec.spl`. `Series<text>` exposes a `str` accessor struct (composition, not inheritance). Methods:
- `s.str.lower() -> Series<text>`
- `s.str.upper() -> Series<text>`
- `s.str.contains(pat: text) -> Series<Bool>`
- `s.str.split(sep: text) -> Series<text>` — splits each element; joins with separator for non-list return (simplified: return joined or first token only in v1.1)
Delegate character ops to `std.common.text`.  
Deliverable: `str_accessor.spl`; spec passes.  
Estimate: 1 day

**T-DF-35** — Spec + Impl: `drop_duplicates`, `set_index`, `reset_index`  
Phase: v1.1  
Dep: T-DF-19 (sort infrastructure), T-DF-32 (unique)  
Action: Write `spec/index_dedup_spec.spl`. Assertions:
- `df.drop_duplicates(subset: [Symbol]) -> DataFrame` — keeps first occurrence; uses sort+dedup on subset columns
- `df.set_index(col: Symbol) -> Result<DataFrame, DfError>` — promotes column to `_index`; removes column from schema
- `df.reset_index() -> DataFrame` — demotes `_index` back to column "index"; resets `_index` to `[0, 1, 2, ...]`  
Deliverable: Spec + impl; spec passes.  
Estimate: 1 day

---

### Phase N — Perf-sugar capture and v1.1 acceptance gate

**T-DF-36** — Perf-sugar capture pass  
Phase: v1.1 (after all impl tasks)  
Dep: all impl tasks above  
Action: Review all `# TODO(PERF-SUGAR-...)` annotations placed during df impl. For each: ensure a corresponding concrete entry exists in `doc/08_tracking/feature_request/scilib_perf_sugar.md` with: title, repro path (spec file + line), measured cost observation (or "anticipated" if interp limit not hit), proposed fix, estimated impact. Update PERF-SUGAR-005/006/007 entries from "anticipated" to "observed" or "fixed". Must not leave any `# TODO` without a tracking entry.  
Deliverable: `scilib_perf_sugar.md` updated.  
Estimate: 0.5 day

**T-DF-37** — v1.1 acceptance gate verification  
Phase: v1.1 final gate  
Dep: T-DF-36 and all spec tasks  
Action: Run `bin/simple test src/lib/nogc_sync_mut/df/` in interpreter mode. Confirm:
- Zero `skip()`
- Zero TODO→NOTE conversions
- Zero primitive type leaks (`f64`/`i64`/`bool`/`str` must not appear in any public signature)
- `DataFrame.from_csv`, `DataFrame.groupby(...).sum()` (lazy RowRange), `df.filter`, `df.select` specs green
- `PERF-SUGAR-005` status = `fixed` or formal deferral documented
- `PERF-SUGAR-006` status = `fixed` or `Symbol = text` fallback documented
- `Tensor = NDArray` alias removed from any df-internal usage (df must reference `NDArray<T>` directly)
If any spec fails: fix at root cause. No weakened assertions.  
Deliverable: All df specs green; gate checklist in `state.md` Phase 3-arch v1.1→v2 section updated.  
Estimate: 0.5 day

---

## Summary Table

| ID | Title | Est | Phase | Deps |
|----|-------|-----|-------|------|
| T-DF-01 | Verify PERF-SUGAR-005 strided-view | 0.5d | v1.1 gate | T-NDARRAY |
| T-DF-02 | Symbol intern verify/fallback | 0.5d | v1.1 gate | — |
| T-DF-03 | PERF-SUGAR-007 lazy-groupby risk | 0.25d | v1.1 gate | T-DF-01 |
| T-DF-04 | Spec: Series<T> construction | 0.5d | v1.1 | T-DF-02 |
| T-DF-05 | Impl: Series/DataFrame/SeriesErased types | 1.5d | v1.1 | T-DF-02, T-DF-04 |
| T-DF-06 | Spec: DataFrame.from_cols | 0.5d | v1.1 | T-DF-05 |
| T-DF-07 | Impl: from_cols, from_ndarray, DfError | 1d | v1.1 | T-DF-05, T-DF-06 |
| T-DF-08 | Spec: column select + multi-select | 0.5d | v1.1 | T-DF-07 |
| T-DF-09 | Impl: col/select/iloc/loc/at/iat | 1.5d | v1.1 | T-DF-07, T-DF-08 |
| T-DF-10 | Spec: df.filter boolean mask | 0.5d | v1.1 | T-DF-09 |
| T-DF-11 | Impl: df.filter | 1d | v1.1 | T-DF-09, T-DF-10 |
| T-DF-12 | Spec: assign/drop/rename/dtypes/astype | 0.5d | v1.1 | T-DF-09 |
| T-DF-13 | Impl: assign/drop/rename/dtypes/astype | 1.5d | v1.1 | T-DF-07, T-DF-12 |
| T-DF-14 | Spec: scalar broadcast on Series<T> | 0.5d | v1.1 | T-DF-05 |
| T-DF-15 | Impl: Series scalar broadcast methods | 1d | v1.1 | T-DF-05, T-DF-14 |
| T-DF-16 | Spec: isna/fillna/dropna | 0.5d | v1.1 | T-DF-09, T-DF-11 |
| T-DF-17 | Impl: is_na, fill_na, drop_na + NaHow | 1.5d | v1.1 | T-DF-09, T-DF-16 |
| T-DF-18 | Spec: sort_values/head/tail/describe/info | 0.5d | v1.1 | T-DF-09 |
| T-DF-19 | Impl: sort_values/head/tail/describe/info | 1.5d | v1.1 | T-DF-17, T-DF-18 |
| T-DF-20 | Spec: groupby lazy RowRange | 0.5d | v1.1 | T-DF-09, T-DF-11, T-DF-03 |
| T-DF-21 | Impl: groupby/GroupBy/RowRange engine | 2d | v1.1 | T-DF-07, T-DF-20 |
| T-DF-22 | Spec: concat row/col | 0.5d | v1.1 | T-DF-07 |
| T-DF-23 | Impl: concat | 1d | v1.1 | T-DF-07, T-DF-22 |
| T-DF-24 | Spec: merge inner/left/right/outer | 0.5d | v1.1 | T-DF-21 |
| T-DF-25 | Impl: merge (sort-merge join) | 2d | v1.1 | T-DF-21, T-DF-24 |
| T-DF-26 | Spec+Impl: df.join (wrapper) | 0.5d | v1.1 | T-DF-25 |
| T-DF-27 | Spec: read_csv dtype inference | 0.5d | v1.1 | T-DF-07 |
| T-DF-28 | Impl: dtype inference + read_csv | 1.5d | v1.1 | T-DF-17, T-DF-27 |
| T-DF-29 | Spec+Impl: to_csv | 1d | v1.1 | T-DF-27 |
| T-DF-30 | Stub: read_parquet (deferred v2) | 0.25d | v1.1 | T-DF-07 |
| T-DF-31 | Spec+Impl: Series.map<U> | 1d | v1.1 | T-DF-05 |
| T-DF-32 | Spec+Impl: value_counts/unique/nunique | 1d | v1.1 | T-DF-05 |
| T-DF-33 | Spec+Impl: df.apply | 1d | v1.1 | T-DF-05, T-DF-31 |
| T-DF-34 | Spec+Impl: Series<text>.str accessor | 1d | v1.1 | T-DF-05 |
| T-DF-35 | Spec+Impl: drop_duplicates/set_index/reset_index | 1d | v1.1 | T-DF-19, T-DF-32 |
| T-DF-36 | Perf-sugar capture pass | 0.5d | v1.1 final | all impl |
| T-DF-37 | v1.1 acceptance gate | 0.5d | v1.1 final | T-DF-36 |

**Total: 37 tasks**

---

## Three Highest-Risk Tasks

### R-1: T-DF-21 — Groupby engine (hash-aggregate / RowRange)

The groupby engine has three simultaneous risk factors: (a) it depends on `NDArray.argsort` landing in the ndarray area — if sort is missing, the sort-then-range strategy falls back to a linear scan O(n) per group; (b) strided column views (PERF-SUGAR-005) are the O(1) access path — without them, every group aggregation is an O(group_size) copy; (c) the generic `agg(f: fn(NDArray<Float64>) -> Float64)` parameter hits PERF-SUGAR-003 (generic fn dispatch boxing in interpreter mode), which may force deferral of user-supplied aggregators to v2. Mitigation: ship `sum` + `mean` as hand-specialized methods in v1.1; gate generic `agg` on PERF-SUGAR-003 resolution.

### R-2: T-DF-28 — `read_csv` dtype inference

Dtype inference over raw text cells is a correctness trap. The two-pass (Int64 → Float64 → text) strategy handles the common case but fails silently on: mixed-type columns that look numeric (e.g., a column with "12", "3.5", "N/A" — first cell is int, but column is float with NA); columns with locale-specific decimal separators; very large files where two-pass doubles memory allocation. Wrong inference corrupts downstream analysis without an error. Risk mitigation: the NA string set ("", "N/A", "nan", "NaN", "null") must be configurable (add `na_values: [text]` parameter with a sensible default); inference failures on individual cells must set the NA mask, never crash.

### R-3: T-DF-15 — Broadcast scalar→Series dispatch

`Series<T>.add_scalar(rhs: T) -> Series<T>` requires that the operator overload `+` on `Series<Float64>` with a `Float64` RHS dispatches to `add_scalar`. In interpreter mode, PERF-SUGAR-003 (generic dispatch boxing) means that `fn add_scalar<T>` may not dispatch correctly when `T = Float64` vs `T = Int64` — the interpreter erases type parameters and boxes arguments. If overloaded `+` dispatch also fails for the same reason, users get a confusing "method not found" or silent wrong-type fallback. Mitigation: implement concrete overloads (`Series<Float64>.add_scalar`, `Series<Int64>.add_scalar`) not a generic; test dispatch in the spec for both dtypes; file PERF-SUGAR-003 observation if dispatch fails.

---

## Files Created by This Area

```
src/lib/nogc_sync_mut/df/
  types.spl          # Series<T>, DataFrame, SeriesErased, Symbol, DfValue, DfError, NaHow, ConcatAxis, JoinHow, ApplyAxis
  construct.spl      # from_cols, from_ndarray
  ops.spl            # col/select/filter/iloc/loc/at/iat/assign/drop/rename/dtypes/astype/sort_values/head/tail/describe/info/concat/drop_duplicates/set_index/reset_index/apply
  series_ops.spl     # Series scalar broadcast, map<U>, value_counts, unique, nunique
  str_accessor.spl   # Series<text>.str accessor
  groupby.spl        # RowRange, GroupBy, DataFrame.groupby
  merge.spl          # merge, df.join
  io.spl             # read_csv (with infer_dtype), to_csv, read_parquet stub
  mod.spl            # re-exports
  spec/
    series_construct_spec.spl
    dataframe_construct_spec.spl
    indexing_spec.spl
    filter_spec.spl
    column_ops_spec.spl
    series_scalar_spec.spl
    missing_spec.spl
    inspect_sort_spec.spl
    groupby_spec.spl
    concat_spec.spl
    merge_spec.spl
    join_spec.spl
    csv_spec.spl
    to_csv_spec.spl
    series_map_spec.spl
    series_counts_spec.spl
    apply_spec.spl
    str_accessor_spec.spl
    index_dedup_spec.spl
```

## Explicitly Out of Scope (handled by sibling areas)

| Item | Owner |
|------|-------|
| `NDArray<T>` struct, `Shape`, `Index`, `Float64`, `Int64`, `Bool` wrappers | `scilib_port_ndarray.md` |
| `NDArray.argsort`, `NDArray.gather`, `NDArray.concat`, strided views | `scilib_port_ndarray.md` |
| `PERF-SUGAR-001` (typed buffer ctor) | `scilib_port_perf_sugar.md` |
| `PERF-SUGAR-003` (generic dispatch) | `scilib_port_perf_sugar.md` |
| `PERF-SUGAR-005` (strided view) | `scilib_port_perf_sugar.md` |
| `PERF-SUGAR-006` (symbol intern) | `scilib_port_perf_sugar.md` |
| math{} block extensions | `scilib_port_math_block.md` |
| `std.ml` Estimator/Transformer/Pipeline | `scilib_port_ml.md` |
| `read_parquet` full implementation | v2 (pending libparquet FFI) |
| `df.rolling`, `df.pivot_table`, `df.melt` | v2 (window/reshape ops) |
| `Series<DateTime>.dt` accessor, `to_datetime` | v2 (datetime type not defined in v1.1) |
| `df.plot` | v2 (requires `std.ui` dep) |
| cuDF backend | v2 (RAPIDS ABI not stable for extern C) |
