# Statistics Library Implementation Plan

**Date:** 2026-01-17
**Status:** Draft
**Feature IDs:** TBD (Pending issue creation)
**Related Research:** `doc/research/statistics_library.md`

---

## 1. Overview

This plan outlines the implementation of a statistics library for Simple, including:
- Collection statistics (Array/Vec)
- DataFrame type with columnar storage
- TQL (Table Query Language) query syntax
- Aggregation and grouping operations
- Future CUDA backend support

---

## 2. Corrected Specification

### 2.1 Table Type Definition (Fixed)

```simple
# Using <> for generics (not [])
Table<Schema>

# Where Schema is a structural type
{
    id: Int,
    age: Float,
    city: Str
}

# Full type
Table<{id: Int, age: Float, city: Str}>
```

### 2.2 Column Type (Fixed)

```simple
# Column wrapper for typed columns
Column<T>

# Properties:
# - Vectorized storage
# - Immutable (transformations produce new columns)
# - Backend-controlled storage location
```

### 2.3 Table Construction (Fixed)

```simple
# Row-oriented (SDN-compatible)
val users = sdn_table |id, age, city|:
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"

# Column-oriented (DataFrame)
val df = dataframe:
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]
```

### 2.4 TQL Query Syntax (Unified Block)

TQL supports both `{}` and `:` block styles with a common `BlockProcessor` interface:

```simple
# Brace style with 'from' inside
val adults = tql {
    from users
    select @id, @age
    where @age >= 18
}

# Indent style with 'from' inside
val adults = tql:
    from users
    select @id, @age
    where @age >= 18

# Method chain style (source already known)
val adults = users.tql {
    select @id, @age
    where @age >= 18
}

val adults = users.tql:
    select @id, @age
    where @age >= 18

# @ prefix for column references
# Outer variables accessed without prefix
val threshold = 18
val adults = tql {
    from users
    where @age >= threshold
}
```

### 2.5 TQL Grammar (Unified Block, LL(1)-Friendly)

```
# Unified block syntax - both styles share BlockProcessor interface
Block := IndentBlock | BraceBlock
IndentBlock := ":" INDENT Statement+ DEDENT
BraceBlock  := "{" Statement+ "}"

TqlBlock
  := "tql" Block                    # Standalone with 'from' inside
  |  Expr ".tql" Block              # Method chain (source is receiver)

TqlStmt
  := FromStmt
   | SelectStmt
   | WhereStmt
   | GroupByStmt
   | OrderByStmt
   | LimitStmt
   | JoinStmt
   | AggStmt

FromStmt    := "from" Expr NEWLINE
SelectStmt  := "select" ColumnList NEWLINE
             | "select" "*" NEWLINE
WhereStmt   := "where" BoolExpr NEWLINE
GroupByStmt := "groupby" ColumnList NEWLINE
OrderByStmt := "orderby" ColumnList ("asc"|"desc")? NEWLINE
LimitStmt   := "limit" IntLiteral NEWLINE
JoinStmt    := "join" Expr "on" BoolExpr NEWLINE
AggStmt     := "agg" Block          # Nested block (either style)

AggBinding  := IDENT ":" AggFunc NEWLINE
AggFunc     := IDENT "(" ColumnRef? ("," Expr)* ")"

ColumnRef   := "@" IDENT
             | "@" IDENT "." IDENT  # For joins: @users.id
ColumnList  := ColumnRef ("," ColumnRef)*
```

### 2.6 Statistics Functions (Complete List)

#### Descriptive Statistics
| Function | Signature | Description |
|----------|-----------|-------------|
| `count()` | `() -> u64` | Number of elements |
| `sum(col)` | `(Column<Num>) -> Num` | Sum of elements |
| `mean(col)` | `(Column<Num>) -> f64` | Arithmetic mean |
| `min(col)` | `(Column<T: Ord>) -> T` | Minimum value |
| `max(col)` | `(Column<T: Ord>) -> T` | Maximum value |
| `var(col)` | `(Column<Num>) -> f64` | Population variance |
| `std(col)` | `(Column<Num>) -> f64` | Population std deviation |
| `skew(col)` | `(Column<Num>) -> f64` | Skewness |
| `kurt(col)` | `(Column<Num>) -> f64` | Kurtosis |

#### Order Statistics
| Function | Signature | Description |
|----------|-----------|-------------|
| `median(col)` | `(Column<Num>) -> f64` | Median (50th percentile) |
| `quantile(col, p)` | `(Column<Num>, f64) -> f64` | p-quantile (0 <= p <= 1) |
| `percentile(col, p)` | `(Column<Num>, f64) -> f64` | p-percentile (0 <= p <= 100) |
| `hist(col, bins)` | `(Column<Num>, u64) -> Histogram` | Histogram with n bins |

#### Inferential Statistics
| Function | Signature | Description |
|----------|-----------|-------------|
| `zscore(col)` | `(Column<Num>) -> Column<f64>` | Z-score normalization |
| `ci(col, level)` | `(Column<Num>, f64) -> (f64, f64)` | Confidence interval |
| `ttest(col)` | `(Column<Num>) -> TTestResult` | One-sample t-test |
| `cov(x, y)` | `(Column<Num>, Column<Num>) -> f64` | Covariance |
| `corr(x, y)` | `(Column<Num>, Column<Num>) -> f64` | Pearson correlation |

#### Predictive Analytics
| Function | Signature | Description |
|----------|-----------|-------------|
| `trend(col)` | `(Column<Num>) -> f64` | Linear trend slope |
| `regress(y, x)` | `(Column<Num>, Column<Num>) -> Regression` | Simple linear regression |
| `ewma(col, alpha)` | `(Column<Num>, f64) -> Column<f64>` | Exponential weighted moving avg |
| `predict(col, window)` | `(Column<Num>, u64) -> f64` | Simple prediction |
| `anomaly(col)` | `(Column<Num>) -> Column<Bool>` | Anomaly detection (IQR-based) |

### 2.7 Complete Example (Fixed)

```simple
val city_stats = tql(users):
    groupby @city
    agg:
        n: count()
        avg_age: mean(@age)
        std_age: std(@age)
        slope: trend(@age)
        q95: quantile(@age, 0.95)

# Result type:
# Table<{
#     city: Str,
#     n: u64,
#     avg_age: f64,
#     std_age: f64,
#     slope: f64,
#     q95: f64
# }>
```

---

## 3. Implementation Phases

### Phase 1: Collection Statistics (P0)
**Goal:** Add statistics functions to Array and Vec types

**Files to Create:**
- `simple/std_lib/src/compiler_core/stats.spl` - Statistics trait and implementations

**API:**
```simple
trait Summarizable<T>:
    fn count() -> u64
    fn sum() -> T
    fn mean() -> f64
    fn min() -> Option<T>
    fn max() -> Option<T>

trait Statistical<T>: Summarizable<T>:
    fn variance() -> f64
    fn std() -> f64
    fn median() -> f64
    fn quantile(p: f64) -> f64

impl Statistical<f64> for [f64]
impl Statistical<i64> for [i64]
impl Statistical<i32> for [i32]
```

**Tests:**
- `simple/std_lib/test/features/stats/collection_stats_spec.spl`

### Phase 2: DataFrame Type (P1)
**Goal:** Column-oriented data structure for analytics

**Files to Create:**
- `simple/std_lib/src/data/__init__.spl` - Module root
- `simple/std_lib/src/data/column.spl` - Column<T> type
- `simple/std_lib/src/data/dataframe.spl` - DataFrame type
- `simple/std_lib/src/data/schema.spl` - Schema introspection

**API:**
```simple
struct Column<T>:
    _data: [T]
    _name: Str

struct DataFrame:
    _columns: Map<Str, Column<Any>>
    _schema: Schema

impl DataFrame:
    static fn new() -> DataFrame
    fn add_column<T>(name: Str, data: [T]) -> DataFrame
    fn get_column<T>(name: Str) -> Option<Column<T>>
    fn select(cols: [Str]) -> DataFrame
    fn filter(pred: fn(Row) -> Bool) -> DataFrame
    fn len() -> u64
```

**Tests:**
- `simple/std_lib/test/features/data/dataframe_spec.spl`

### Phase 3: TQL Parser (P1)
**Goal:** Parse TQL query blocks

**Files to Modify:**
- `src/parser/src/expressions/` - Add TQL block parsing
- `src/parser/src/ast/nodes/` - Add TQL AST nodes

**AST Nodes:**
```rust
enum TqlStatement {
    Select { columns: Vec<ColumnRef> },
    Where { condition: Expr },
    GroupBy { columns: Vec<ColumnRef> },
    OrderBy { columns: Vec<ColumnRef>, descending: bool },
    Limit { count: u64 },
    Aggregate { bindings: Vec<AggBinding> },
}

struct TqlBlock {
    source: Expr,
    statements: Vec<TqlStatement>,
}
```

**Tests:**
- `src/parser/tests/tql_parsing.rs`

### Phase 4: TQL Execution (P2)
**Goal:** Execute TQL queries on DataFrames

**Files to Create:**
- `simple/std_lib/src/data/tql.spl` - TQL executor
- `simple/std_lib/src/data/aggregation.spl` - Aggregation functions

**Logical Plan:**
```simple
enum LogicalPlan:
    Scan(source: DataFrame)
    Filter(pred: Predicate, input: Box<LogicalPlan>)
    Project(cols: [Str], input: Box<LogicalPlan>)
    GroupBy(groups: [Str], aggs: [Aggregation], input: Box<LogicalPlan>)
    Sort(cols: [Str], desc: Bool, input: Box<LogicalPlan>)
    Limit(n: u64, input: Box<LogicalPlan>)
```

**Tests:**
- `simple/std_lib/test/features/data/tql_execution_spec.spl`

### Phase 5: Advanced Statistics (P2)
**Goal:** Quantiles, distributions, correlations

**Files to Create:**
- `simple/std_lib/src/data/statistics.spl` - Full statistics library

**API:**
```simple
fn median<T: Ord + Num>(col: Column<T>) -> f64
fn quantile<T: Ord + Num>(col: Column<T>, p: f64) -> f64
fn cov<T: Num>(x: Column<T>, y: Column<T>) -> f64
fn corr<T: Num>(x: Column<T>, y: Column<T>) -> f64
fn zscore<T: Num>(col: Column<T>) -> Column<f64>
```

**Tests:**
- `simple/std_lib/test/features/stats/advanced_stats_spec.spl`

### Phase 6: CUDA Backend (P3)
**Goal:** GPU-accelerated statistics

**Files to Create:**
- `simple/std_lib/src/data/backend/__init__.spl`
- `simple/std_lib/src/data/backend/cpu.spl`
- `simple/std_lib/src/data/backend/cuda.spl`

**Backend Trait:**
```simple
trait TableBackend:
    fn scan(source: DataFrame) -> Iterator<Row>
    fn filter(pred: Predicate) -> Self
    fn project(cols: [Str]) -> Self
    fn aggregate(groups: [Str], aggs: [Aggregation]) -> Self
    fn sort(cols: [Str], desc: Bool) -> Self
    fn supports_gpu() -> Bool
```

**Tests:**
- `simple/std_lib/test/features/data/cuda_backend_spec.spl`

---

## 4. Dependencies

### Internal Dependencies
- SDN Parser (`src/sdn/`) - For table literal parsing
- Type System (`src/type/`) - For schema type checking
- Tensor Statistics (`simple/std_lib/src/ml/torch/`) - Reference implementation

### External Dependencies (Future)
- Arrow format support (for columnar storage)
- CUDA toolkit (for GPU backend)

---

## 5. Testing Strategy

### Unit Tests
- Each phase includes unit tests in `simple/std_lib/test/unit/`
- Rust parser tests in `src/*/tests/`

### Integration Tests
- Feature specs in `simple/std_lib/test/features/`
- BDD format using SSpec framework

### Performance Tests
- Benchmark suite for statistics on large datasets
- Comparison between CPU and GPU backends

---

## 6. Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| TQL parser complexity | High | Start with minimal grammar, iterate |
| CUDA FFI challenges | Medium | CPU-first, abstract backend |
| Schema type inference | Medium | Explicit annotations first |
| Performance on large data | Medium | Lazy evaluation, streaming |

---

## 7. Success Criteria

### Phase 1 Complete When:
- [ ] `mean()`, `std()`, `var()`, `min()`, `max()` work on arrays
- [ ] All collection stats tests pass
- [ ] Documentation in stdlib

### Phase 2 Complete When:
- [ ] DataFrame can be constructed from column arrays
- [ ] Basic select/filter operations work
- [ ] Schema introspection available

### Phase 3 Complete When:
- [ ] TQL blocks parse without errors
- [ ] AST nodes generated correctly
- [ ] Parser tests pass

### Phase 4 Complete When:
- [ ] TQL queries execute on DataFrames
- [ ] Aggregations produce correct results
- [ ] Integration tests pass

---

## 8. Related Documents

- `doc/research/statistics_library.md` - Research findings
- `doc/spec/stdlib.md` - Stdlib architecture
- `simple/std_lib/test/features/stats/` - Test specifications
