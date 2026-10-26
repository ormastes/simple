# DataFrame Guide — std.df

A pandas-inspired DataFrame library for the Simple language. Provides typed
columnar storage (`Series`), a two-dimensional `DataFrame`, and a set of
row/column operations modelled after the pandas API. All operations return new
values — there are no in-place mutations.

---

## 1. Import

```simple
use std.df.*
use std.ndarray.*   # needed for array_bool, array_i64, DType, Float64, Int64, Index, Bool
```

Both imports are required in most files. `std.ndarray` supplies the typed scalar
wrappers (`Float64`, `Int64`, `Index`, `Bool`) and the array constructors used
to build Series values and boolean masks.

---

## 2. Construction

### From typed columns

`DataFrame.from_columns` is the primary constructor. Each column is wrapped in
`SeriesErased` so the heterogeneous list can be passed as `[SeriesErased]`.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"),
        [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"),
        [Int64.new(5), Int64.new(10), Int64.new(15)])),
]).unwrap()
```

`Series.from_values` infers `DType.I64` for integer-valued `Float64` lists and
`DType.F64` otherwise.

### From rows

`DataFrame.from_rows` accepts a list of `[RowEntry]`, where each row is built
from `RowEntry.new(key, value)` pairs.

```simple
val row0 = [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(1.0))),
            RowEntry.new(Symbol.from("y"), DfValue.I64(Int64.new(10)))]
val df = DataFrame.from_rows([row0]).unwrap()
```

### From CSV text

`from_csv_text` parses a CSV string directly. Integer columns are inferred as
`DType.I64`; fractional columns become `DType.F64`. Blank cells become missing
values.

```simple
val df = from_csv_text("id,score\n1,10.5\n2,20.25").unwrap()
```

### Inspecting shape

```simple
df.num_rows()          # -> Index
df.num_cols()          # -> Index
df.shape()             # -> DataFrameShape { rows: Index, cols: Index }
df.columns()           # -> [Symbol]  (column names in insertion order)
df.dtypes()            # -> SeriesDType
```

---

## 3. Column Operations

### Access a column

```simple
val s: Series = df.col(Symbol.from("price")).unwrap()
val v: Float64 = s.get(Index.new(0))   # read one element
```

### Select a subset of columns

Returns a new DataFrame with only the requested columns, in requested order.

```simple
val sub = df.select([Symbol.from("qty"), Symbol.from("price")]).unwrap()
```

### Add or replace a column

`assign` adds a new column if the name does not exist, or replaces it if it
does. Both return a new `DataFrame`.

```simple
val df2 = df.assign(
    Symbol.from("total"),
    SeriesErased.F64Series(Series.from_values(Symbol.from("total"),
        [Float64.new(5.0), Float64.new(20.0), Float64.new(45.0)]))
)
```

### Rename a column

```simple
val df2 = df.rename(Symbol.from("qty"), Symbol.from("quantity")).unwrap()
```

### Drop a column

```simple
val df2 = df.drop(Symbol.from("price")).unwrap()
```

---

## 4. Row Operations

### Filter with a boolean mask

Build a boolean `NDArray` with `array_bool` and pass it to `filter`. The mask
length must equal `num_rows`.

```simple
val mask = array_bool([Bool.new(true), Bool.new(false), Bool.new(true)])
val filtered = df.filter(mask).unwrap()
```

### Head and tail

```simple
val top2 = df.head(Index.new(2)).unwrap()   # first 2 rows
val bot2 = df.tail(Index.new(2)).unwrap()   # last 2 rows
```

Counts larger than the frame length are clamped to `num_rows`. Negative counts
return `Err(DfError.ShapeMismatch)`.

### Sort

`sort_values` sorts ascending by the named column. All columns are reindexed
together.

```simple
val sorted = df.sort_values(Symbol.from("price")).unwrap()
```

---

## 5. Aggregation

### groupby_sum / groupby_mean

Both methods group by a single key column and aggregate a single numeric value
column. The value column must be `DType.F64`.

```simple
val totals = df.groupby_sum(Symbol.from("team"), Symbol.from("points")).unwrap()
val avgs   = df.groupby_mean(Symbol.from("team"), Symbol.from("points")).unwrap()
```

### value_counts

Returns a two-column DataFrame with the original column name and a `"count"`
column. Values appear in order of first occurrence.

```simple
val vc = value_counts(s)   # s: Series
val count_col = vc.col(Symbol.from("count")).unwrap()
```

### unique / nunique

```simple
val uniq_i64: Series = s.unique_i64()   # deduped Series (I64 column)
val n: Index         = s.nunique()      # count of distinct non-missing values
```

### pivot_sum

Long-to-wide pivot. The `columns` key must be numeric; duplicate `(index, column_key)` pairs are summed. Missing cells are masked.

```simple
# df has columns: id (I64), month (I64), sales (F64)
val wide = df.pivot_sum(
    Symbol.from("id"),
    Symbol.from("month"),
    Symbol.from("sales"),
    Symbol.from("sales")   # prefix for generated column names
).unwrap()
# produces columns: id, sales_0, sales_1, ...
```

Also available as a free function: `pivot_sum(df, index, columns, values, name_prefix)`.

---

## 6. Combining DataFrames

### concat

Concatenates a list of DataFrames along rows or columns.

```simple
# Row concat — schemas and dtypes must match
val tall = concat([df1, df2], ConcatAxis.Rows).unwrap()

# Column concat — row counts must match, no duplicate column names
val wide = concat([df1, df2], ConcatAxis.Cols).unwrap()
```

### merge / join

`merge` joins on a single numeric key column. `JoinHow` controls which rows are
kept: `Inner`, `Left`, `Right`, or `Outer`. Unmatched rows in outer joins have
their missing cells masked.

```simple
val out = merge(left, right, Symbol.from("id"), JoinHow.Inner).unwrap()

# Equivalent convenience method on DataFrame:
val out = left.join(right, Symbol.from("id"), JoinHow.Left).unwrap()
```

---

## 7. Missing Values

Missing values are tracked per element in each `Series` via a `[Bool]` mask.

### Constructing series with missing values

```simple
val s = Series.from_f64_masked(
    Symbol.from("x"),
    [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]   # true = missing
).unwrap()
```

### is_na / fill_na

```simple
val na_series: Series = s.is_na()                    # Bool series, true where missing
val filled:    Series = s.fill_na(Float64.new(0.0))  # replace missing with fill value
```

### drop_na

```simple
val clean = df.drop_na(NaHow.Any)   # drop rows where ANY column is missing
val clean = df.drop_na(NaHow.All)   # drop rows where ALL columns are missing
```

### Testing a specific cell

```simple
val missing: Bool = s.is_missing(Index.new(1)).unwrap()
```

---

## 8. CSV I/O

### Parse CSV text into a DataFrame

```simple
val df = from_csv_text("x,y\n1.5,2.5\n3.0,4.0").unwrap()
```

Column dtypes are inferred: integers become `DType.I64`, fractions become
`DType.F64`. Blank cells (`1.0,`) become masked missing values.

### Serialize a DataFrame to CSV text

```simple
val csv: text = df.to_csv_text().unwrap()
```

The header row is the column names joined with commas. Missing cells are written
as empty fields. Integer values are written without a decimal point; float
values always include at least one decimal place (e.g. `1.0`).

### Round-trip example

```simple
val original = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("x"),
        [Float64.new(1.0), Float64.new(3.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("y"),
        [Int64.new(2), Int64.new(4)])),
]).unwrap()
val csv    = original.to_csv_text().unwrap()
val parsed = from_csv_text(csv).unwrap()
```

---

## Error Handling

All fallible operations return `Result<T, DfError>`. The error enum:

| Variant | Meaning |
|---|---|
| `DfError.ShapeMismatch` | Column lengths differ, mask length wrong, or invalid argument |
| `DfError.ColumnNotFound` | Named column does not exist |
| `DfError.DuplicateColumn` | Column name collision (rename, column concat) |
| `DfError.ParseError` | Malformed CSV input |

Use `.unwrap()` in tests or `.is_err()` / pattern matching in production code.

---

## Source Locations

| File | Contents |
|---|---|
| `src/lib/nogc_sync_mut/df/mod.spl` | Core types, `Series`, `DataFrame`, all methods |
| `src/lib/nogc_sync_mut/df/df_transform.spl` | `merge`, `concat`, `groupby_*`, `pivot_sum`, `value_counts` |
| `src/lib/nogc_sync_mut/df/df_io.spl` | `from_csv_text`, `dataframe_to_csv_text` (`to_csv_text`) |
| `src/lib/nogc_async_mut/df/` | Async facade (same API surface, async I/O) |
| `test/03_system/feature/scilib/` | Spec files covering every operation above |
