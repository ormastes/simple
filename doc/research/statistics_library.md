# Statistics Library Research

**Date:** 2026-01-17
**Status:** Research Complete
**Related Features:** SDN Tables, TQL, Data Analytics

## Executive Summary

This document analyzes the proposed SDN Table, TQL, and Statistics specification against Simple's existing codebase to identify gaps, conflicts, and implementation requirements.

---

## 1. Current State Analysis

### 1.1 What Exists

| Component | Status | Location | Notes |
|-----------|--------|----------|-------|
| SDN Parser | Complete | `src/sdn/` | LL(2) parser, 7 value types |
| SDN Table Value | Complete | `src/sdn/src/value.rs:25-32` | Named tables `\|field\|` syntax |
| SDN Stdlib | Complete | `simple/std_lib/src/sdn/` | 8 modules, 100KB+ |
| SDN-SQL Bridge | Complete | `src/db/src/sdn_table.rs` | Export/import conversion |
| Database Schema | Complete | `src/db/src/schema.rs` | Column introspection |
| Query DSL (SQP) | Complete | `src/sqp/` | Type-safe query builder |
| Tensor Statistics | Complete | `simple/std_lib/src/ml/torch/tensor_class.spl` | mean, std, var, min, max, norm |
| Basic Math | Complete | `simple/std_lib/src/compiler_core/math.spl` | 265 lines, trig/log/exp |

### 1.2 What's Missing

| Component | Status | Priority | Notes |
|-----------|--------|----------|-------|
| DataFrame Type | Missing | P0 | No columnar data structure in stdlib |
| Collection Stats | Missing | P0 | No mean/std/var on arrays |
| Aggregation Ops | Missing | P1 | No group_by, count, sum |
| TQL Query Block | Missing | P1 | Proposed but not implemented |
| Advanced Stats | Missing | P2 | Quantiles, percentiles, distributions |
| CUDA Statistics | Missing | P3 | GPU-accelerated statistics |

---

## 2. Specification Issues Found

### 2.1 Syntax Conflicts

#### Issue #1: Variable Declaration Keyword
**Spec uses:** `let`
**Simple uses:** `val` (immutable), `var` (mutable)

```simple
# WRONG (in spec)
let users = table: ...

# CORRECT (Simple syntax)
val users = table: ...
```

#### Issue #2: Generic Syntax
**Spec uses:** `Table[Schema]`, `Column[T]`
**Simple uses:** `<>` for generics (CLAUDE.md explicitly states `[]` is deprecated)

```simple
# WRONG (deprecated)
Table[{id: Int, age: Float}]
Column[T]
Option[T]

# CORRECT (Simple syntax)
Table<{id: Int, age: Float}>
Column<T>
Option<T>
```

#### Issue #3: SDN Table Syntax Mismatch
**Spec proposes:**
```simple
val users = table:
    id:   [1,2,3]
    age:  [31.0,24.0,28.0]
```

**Current SDN table syntax:**
```sdn
users |id, name, email|
    1, Alice, alice@example.com
    2, Bob, bob@example.com
```

The spec's column-oriented syntax conflicts with SDN's row-oriented named tables.

#### Issue #4: TQL Block Syntax (RESOLVED)
**Original spec proposed:** `tql(users) { ... }` with explicit source parameter

**Corrected design:** Unified block syntax supporting both styles with `from` inside:
```simple
# Brace style
val adults = tql {
    from users
    select @id, @age
    where @age >= 18
}

# Indent style
val adults = tql:
    from users
    select @id, @age
    where @age >= 18

# Method chain style
val adults = users.tql {
    select @id, @age
    where @age >= 18
}
```

Both `{}` and `:` block styles share a common `BlockProcessor` interface.

### 2.2 Grammar Conflicts

#### Issue #5: LL(1) Parsing Concerns
The proposed grammar uses SQL-like keywords that may create parsing ambiguities:

```
SelectStmt := "select" ColumnList
WhereStmt  := "where" BoolExpr
GroupStmt  := "group" "by" ColumnList
```

Simple requires LL(1)-friendly constructs. The `group by` two-keyword sequence needs careful handling.

**Proposed Fix:**
```
GroupStmt := "groupby" ColumnList  # Single keyword
# OR
GroupStmt := "group:" ColumnList   # Colon separator
```

#### Issue #6: Expression Capture Rules
The spec states:
> Inside tql{}: Identifiers resolve only to table columns. No variable capture.

This conflicts with Simple's lexical scoping rules. Need explicit disambiguation:
```simple
tql(users):
    where @age > 25        # @ prefix for column reference
    where age > threshold  # age = column, threshold = outer variable
```

### 2.3 Semantic Issues

#### Issue #7: Statistics Function Overlap
Some proposed functions overlap with existing Tensor methods:

| Function | Tensor Has? | Collection Has? |
|----------|-------------|-----------------|
| `mean()` | Yes | No |
| `std()` | Yes | No |
| `var()` | Yes (as `variance()`) | No |
| `min()` | Yes | No |
| `max()` | Yes | No |
| `sum()` | Yes | No |
| `median()` | No | No |
| `quantile()` | No | No |

**Recommendation:** Unify statistics trait across Tensor, Array, and Column types.

#### Issue #8: Schema Type Definition
The spec doesn't clarify how schema types are defined:

```simple
# Option A: Inline structural type
Table<{id: Int, age: Float}>

# Option B: Named struct
struct UserSchema:
    id: Int
    age: Float

Table<UserSchema>

# Option C: Type alias
type UserTable = Table<{id: Int, age: Float}>
```

Simple should support all three, with Option A for ad-hoc queries.

### 2.4 Backend Claims

#### Issue #9: CUDA Library References
The spec claims:
> CUDA backend is built from: cuDF, CUB, Thrust, cuBLAS, cuSOLVER

**Concerns:**
- cuDF is Python-focused (RAPIDS), not directly callable from compiled code
- Need clarification on FFI strategy
- Consider alternatives: CUTLASS, cuTensor for matrix ops

**Recommendation:** Abstract backend behind trait, implement CPU-first.

---

## 3. Existing Code References

### 3.1 SDN Table Implementation
**File:** `src/sdn/src/value.rs:24-32`
```rust
Table {
    fields: Option<Vec<String>>,  // Named fields
    types: Option<Vec<String>>,   // Type annotations
    rows: Vec<Vec<SdnValue>>,     // Row data
}
```

### 3.2 Tensor Statistics
**File:** `simple/std_lib/src/ml/torch/tensor_class.spl:540-700`
- `sum()`, `mean()`, `min()`, `max()`
- `std()`, `std_dim()` with Bessel's correction
- `variance()`, `variance_dim()`
- `norm()`, `norm_dim()` for Lp norms

### 3.3 Database Schema
**File:** `src/db/src/schema.rs`
```rust
struct ColumnInfo {
    name: String,
    column_type: ColumnType,
    nullable: bool,
    primary_key: bool,
    default_value: Option<String>,
}

enum ColumnType {
    Integer, Real, Text, Blob, Boolean,
    Date, Time, Timestamp, Json, Uuid
}
```

---

## 4. Design Decisions Required

### Decision #1: Column vs Row Orientation
- **Current SDN:** Row-oriented (like CSV)
- **Proposed:** Column-oriented (like Parquet/Arrow)

**Recommendation:** Support both:
- Keep existing SDN row tables for data interchange
- Add new `DataFrame` type for analytics (column-oriented)

### Decision #2: TQL Scope
Options:
1. **Minimal:** Only `select`, `where`, `order`, `limit`
2. **Standard:** Add `group by`, basic aggregations
3. **Full:** Add window functions, CTEs, subqueries

**Recommendation:** Start with Standard scope.

### Decision #3: Statistics Trait Hierarchy
```simple
trait Summarizable<T>:
    fn count() -> u64
    fn sum() -> T
    fn mean() -> f64
    fn min() -> T
    fn max() -> T

trait StatisticallyDistributed<T>: Summarizable<T>:
    fn variance() -> f64
    fn std() -> f64
    fn median() -> T
    fn quantile(p: f64) -> T
```

### Decision #4: Backend Abstraction
```simple
trait TableBackend:
    fn scan(table: Table) -> Iterator<Row>
    fn filter(pred: Predicate) -> Self
    fn project(cols: [ColumnRef]) -> Self
    fn aggregate(groups: [ColumnRef], aggs: [Aggregation]) -> Self
```

---

## 5. Recommendations

### 5.1 Immediate Fixes (Before Implementation)
1. Replace all `let` with `val`/`var`
2. Replace all `[T]` generics with `<T>`
3. Replace `tql(t) { }` with `tql(t):` (indentation-based)
4. Replace `group by` with `groupby` (single keyword)

### 5.2 Design Refinements
1. Add column reference prefix (`@col` or `$col`) for disambiguation
2. Define schema as structural types matching SDN dict syntax
3. Create unified `Statistics` trait for arrays, tensors, columns
4. Abstract backend to enable CPU-first, GPU-later strategy

### 5.3 Implementation Order
1. **Phase 1:** Collection statistics (Array/Vec mean, std, etc.)
2. **Phase 2:** DataFrame type with column storage
3. **Phase 3:** TQL query syntax and parser
4. **Phase 4:** Aggregation and grouping
5. **Phase 5:** CUDA backend

---

## 6. Related Documents

- `doc/spec/stdlib.md` - Stdlib variant model
- `doc/research/sdn_self_hosting.md` - SDN roadmap
- `simple/std_lib/src/ml/torch/tensor_class.spl` - Existing statistics

---

## Appendix A: Corrected Table Literal Syntax

```simple
# SDN-compatible row-oriented table (both styles)
val users = table |id, age, city|:
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"

val users = table |id, age, city| {
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"
}

# Column-oriented DataFrame (both styles)
val df = dataframe:
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]

val df = dataframe {
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]
}
```

## Appendix B: Corrected TQL Syntax (Unified Block)

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

val city_stats = tql {
    from users
    groupby @city
    agg {
        n: count()
        avg_age: mean(@age)
        std_age: std(@age)
    }
}

# Mixed nested styles allowed
val city_stats = tql:
    from users
    groupby @city
    agg {
        n: count()
        avg_age: mean(@age)
    }
```

## Appendix C: Other Custom Blocks

```simple
# Math block
val formula = math {
    f(x) = x^2 + 2*x + 1
    derivative = d/dx f(x)
}

val area = math { pi * r^2 }

# Regex block
val pattern = regex {
    ^(?<user>\w+)@(?<domain>\w+)\.(?<tld>\w+)$
}

# JSON block
val config = json {
    "name": "app",
    "version": "1.0"
}

# HTML block
val page = html {
    div class="container" {
        h1 { "Hello" }
    }
}
```
