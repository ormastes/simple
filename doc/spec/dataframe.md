# Simple SDN Table, TQL, and Statistics

**Static DataFrame Design & Grammar**

---

## 1. Overview

Simple provides a static, SDN-native Table system for structured data processing, analytics, and statistics.

Key properties:

- Tables are first-class SDN values
- Queries are written using `tql(source):` custom blocks
- Statistics and predictions are deterministic and static
- Execution targets CPU or CUDA backends
- No runtime SQL, no string DSL, no dynamic schema mutation

This system is designed for compile-time analyzable analytics.

---

## 2. SDN Table Type

### 2.1 Table Type Definition

A table is represented as:

```simple
Table<Schema>
```

Where `Schema` is an SDN structural type:

```simple
{
    id: Int,
    age: Float,
    city: Str
}
```

Properties:

- Column-oriented storage
- Schema known at compile time
- Immutable (transformations produce new tables)
- Compatible with CPU and GPU backends

---

### 2.2 Column Semantics

Each column is a vector:

```simple
Column<T>
```

Rules:

- No scalar indexing in language surface
- All operations are vectorized
- Storage location (CPU/GPU) is backend-controlled

---

## 3. Table Construction Grammar

### 3.1 Row-Oriented Table Literal (SDN-Compatible)

```simple
val users = sdn_table |id, age, city|:
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"
```

Rules:

- Uses existing SDN named-table syntax
- All rows must have same column count
- Types inferred from literals
- Produces `Table<{id: Int, age: Float, city: Str}>`

### 3.2 Column-Oriented DataFrame Literal

```simple
val users = dataframe:
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]
```

Rules:

- All columns must have equal length
- Types inferred from array literals
- Produces `Table<{id: Int, age: Float, city: Str}>`

---

### 3.3 External Sources

```simple
val data = read_csv("users.csv")
```

- Schema inferred or provided
- Execution deferred until materialization

---

## 4. Table Query Language (tql)

### 4.1 Definition

`tql(source):` is a custom block that defines a static table query and analytics plan.

```simple
val adults = tql(users):
    select @id, @age
    where @age >= 18
```

Properties:

- Parsed at compile time
- Schema validated statically
- Produces a new `Table<...>`
- No runtime interpretation
- Uses `@` prefix for column references

---

### 4.2 Grammar (LL(1)-Friendly)

```
TqlBlock
  := "tql" "(" Expr ")" ":" INDENT TqlStmt+ DEDENT

TqlStmt
  := SelectStmt
   | WhereStmt
   | GroupByStmt
   | OrderByStmt
   | LimitStmt
   | AggStmt

SelectStmt  := "select" ColumnList NEWLINE
             | "select" "*" NEWLINE

WhereStmt   := "where" BoolExpr NEWLINE

GroupByStmt := "groupby" ColumnList NEWLINE

OrderByStmt := "orderby" ColumnList ("asc" | "desc")? NEWLINE

LimitStmt   := "limit" IntLiteral NEWLINE

AggStmt     := "agg" ":" INDENT AggBinding+ DEDENT

AggBinding  := IDENT ":" AggExpr NEWLINE

ColumnRef   := "@" IDENT
ColumnList  := ColumnRef ("," ColumnRef)*
```

Each statement starts with a distinct keyword, allowing one-pass parsing.

---

## 5. Expressions in tql

### 5.1 Column Resolution Rules

Inside `tql(source):`:

- Column references use `@` prefix: `@age`, `@city`
- Outer variables accessed without prefix
- No mutation or assignment

```simple
val threshold = 25
val adults = tql(users):
    where @age > threshold  # @age = column, threshold = variable
```

---

### 5.2 Expression Subset

```
Expr
  := ColumnRef
   | Literal
   | Ident              # outer variable
   | Expr ("+" | "-" | "*" | "/" | "%" ) Expr
   | Expr ("==" | "!=" | "<" | "<=" | ">" | ">=") Expr
   | Expr ("and" | "or") Expr
   | "not" Expr
   | "(" Expr ")"
```

All column expressions are vectorized.

---

## 6. Statistics & Analytics

### 6.1 Descriptive Statistics

Supported aggregation functions:

| Function | Signature | Description |
|----------|-----------|-------------|
| `count()` | `() -> u64` | Count of rows |
| `sum(col)` | `(@Col) -> Num` | Sum of values |
| `mean(col)` | `(@Col) -> f64` | Arithmetic mean |
| `min(col)` | `(@Col) -> T` | Minimum value |
| `max(col)` | `(@Col) -> T` | Maximum value |
| `var(col)` | `(@Col) -> f64` | Population variance |
| `std(col)` | `(@Col) -> f64` | Population std deviation |
| `skew(col)` | `(@Col) -> f64` | Skewness |
| `kurt(col)` | `(@Col) -> f64` | Kurtosis |

---

### 6.2 Order Statistics

| Function | Signature | Description |
|----------|-----------|-------------|
| `median(col)` | `(@Col) -> f64` | Median (50th percentile) |
| `quantile(col, p)` | `(@Col, f64) -> f64` | p-quantile (0 <= p <= 1) |
| `percentile(col, p)` | `(@Col, f64) -> f64` | p-percentile (0 <= p <= 100) |
| `hist(col, bins)` | `(@Col, u64) -> Histogram` | Histogram with n bins |

---

### 6.3 Inferential Statistics

| Function | Signature | Description |
|----------|-----------|-------------|
| `zscore(col)` | `(@Col) -> Column<f64>` | Z-score normalization |
| `ci(col, level)` | `(@Col, f64) -> (f64, f64)` | Confidence interval |
| `ttest(col)` | `(@Col) -> TTestResult` | One-sample t-test |
| `cov(x, y)` | `(@Col, @Col) -> f64` | Covariance |
| `corr(x, y)` | `(@Col, @Col) -> f64` | Pearson correlation |

---

### 6.4 Predictive (Deterministic) Analytics

`tql` supports value-producing predictions, not model training:

| Function | Signature | Description |
|----------|-----------|-------------|
| `trend(col)` | `(@Col) -> f64` | Linear trend slope |
| `regress(y, x)` | `(@Col, @Col) -> Regression` | Simple linear regression |
| `ewma(col, alpha)` | `(@Col, f64) -> Column<f64>` | Exponential weighted MA |
| `predict(col, window)` | `(@Col, u64) -> f64` | Simple prediction |
| `anomaly(col)` | `(@Col) -> Column<Bool>` | Anomaly detection (IQR) |

All results are scalars or columns.

---

### 6.5 Statistics Usage Example

```simple
val city_stats = tql(users):
    groupby @city
    agg:
        n: count()
        avg_age: mean(@age)
        std_age: std(@age)
        slope: trend(@age)
        q95: quantile(@age, 0.95)
```

Result schema:

```simple
Table<{
    city: Str,
    n: u64,
    avg_age: f64,
    std_age: f64,
    slope: f64,
    q95: f64
}>
```

---

## 7. Execution Model

### 7.1 Lazy Semantics

`tql(source):` constructs a logical plan.

Execution is triggered by:

- `print(result)`
- `result.collect()`
- Output operations

---

### 7.2 Logical Plan Nodes

```simple
enum LogicalPlan:
    Scan(source: Table)
    Filter(pred: Predicate, input: Box<LogicalPlan>)
    Project(cols: [Str], input: Box<LogicalPlan>)
    GroupBy(groups: [Str], aggs: [Aggregation], input: Box<LogicalPlan>)
    Sort(cols: [Str], desc: Bool, input: Box<LogicalPlan>)
    Limit(n: u64, input: Box<LogicalPlan>)
```

Statistics compile into aggregation kernels.

---

## 8. Backend Architecture

### 8.1 Backend Abstraction

```simple
trait TableBackend:
    fn scan(source: Table) -> Iterator<Row>
    fn filter(pred: Predicate) -> Self
    fn project(cols: [Str]) -> Self
    fn groupby(groups: [Str], aggs: [Aggregation]) -> Self
    fn aggregate(aggs: [Aggregation]) -> Self
    fn sort(cols: [Str], desc: Bool) -> Self
    fn supports_gpu() -> Bool
```

Implementations:

- `CpuBackend`
- `CudaBackend`

---

### 8.2 CUDA Backend

CUDA backend may leverage:

- Column-oriented GPU memory layout
- Parallel reduction kernels
- Thrust-style algorithms
- cuBLAS for linear algebra operations

Statistics are implemented as compiled kernel graphs, not library calls.

---

## 9. GPU Capability & Fallback

Each operation declares:

```simple
struct OpCapability:
    supports_gpu: Bool
    approximate_gpu: Bool
```

Compiler behavior:

- Keep full plan on GPU when possible
- Split plan explicitly if required
- CPU fallback is visible and analyzable

---

## 10. Memory Model

- Columnar buffers
- Explicit CPU <-> GPU transfer nodes
- No implicit synchronization
- Arrow-compatible layout

---

## 11. Determinism Guarantees

`tql` guarantees:

- Deterministic execution
- No hidden randomness
- No mutable state
- Stable schema

This enables:

- Formal reasoning
- Cost modeling
- Future verification

---

## 12. Explicit Non-Goals

The following are intentionally excluded:

- Runtime SQL parsing
- Pandas-style mutable DataFrames
- Dynamic schema mutation
- Stateful ML training

These belong to future `model{}` / `train{}` blocks.

---

## 13. Summary

| Component | Description |
|-----------|-------------|
| SDN Table | Row-oriented data interchange format |
| DataFrame | Column-oriented analytics type |
| `tql(t):` | Static query + analytics IR |
| Statistics | Deterministic aggregation kernels |
| CUDA | Explicit, composable GPU support |

This design keeps Simple fast, analyzable, and compiler-driven.

---

## Related Documents

- `doc/research/statistics_library.md` - Research findings
- `doc/plan/statistics_library_implementation.md` - Implementation plan
- `simple/std_lib/test/features/stats/table_statistics_spec.spl` - Test specification
