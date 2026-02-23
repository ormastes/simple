# Simple SDN Table, TQL, and Statistics

**Static DataFrame Design & Grammar**

---

## 1. Overview

Simple provides a static, SDN-native Table system for structured data processing, analytics, and statistics.

Key properties:

- Tables are first-class SDN values
- Queries are written using `tql` custom blocks
- Statistics and predictions are deterministic and static
- Execution targets CPU or CUDA backends
- No runtime SQL, no string DSL, no dynamic schema mutation

This system is designed for compile-time analyzable analytics.

---

## 2. Unified Block Syntax

Simple supports two equivalent block styles that share a common processing interface:

### 2.1 Block Styles

```simple
# Style A: Indentation-based (Python-like)
val result = tql:
    from users
    select @id, @age

# Style B: Brace-based (Rust/C-like)
val result = tql {
    from users
    select @id, @age
}

# Both produce identical AST and behavior
```

### 2.2 Unified Block Grammar

```
Block := IndentBlock | BraceBlock

IndentBlock := ":" INDENT Statement+ DEDENT
BraceBlock  := "{" Statement+ "}"

CustomBlock := BlockKeyword Block
            |  Expr "." BlockKeyword Block

BlockKeyword := "tql" | "math" | "regex" | "html" | "css" | "json" | ...
```

### 2.3 Common Block Interface

All custom blocks implement a shared processing interface:

```simple
trait BlockProcessor<Input, Output>:
    fn parse(block: BlockNode) -> Result<Input, ParseError>
    fn validate(input: Input) -> Result<Input, ValidationError>
    fn compile(input: Input) -> Output
```

This enables:
- Consistent syntax across all DSL blocks
- Shared tooling (formatters, linters)
- Unified error reporting
- Mixed block styles in same file

### 2.4 Nested Block Styles

Nested blocks can use different styles:

```simple
val result = tql {
    from users
    groupby @city
    agg:                    # Indent inside braces
        n: count()
        avg: mean(@age)
}

val result2 = tql:
    from users
    groupby @city
    agg {                   # Braces inside indent
        n: count()
        avg: mean(@age)
    }
```

---

## 3. SDN Table Type

### 3.1 Table Type Definition

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

### 3.2 Column Semantics

Each column is a vector:

```simple
Column<T>
```

Rules:

- No scalar indexing in language surface
- All operations are vectorized
- Storage location (CPU/GPU) is backend-controlled

---

## 4. Table Construction

### 4.1 Row-Oriented Table Literal (SDN-Compatible)

```simple
# Indentation style
val users = table |id, age, city|:
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"

# Brace style
val users = table |id, age, city| {
    1, 31.0, "Seoul"
    2, 24.0, "Busan"
    3, 28.0, "Seoul"
}
```

Rules:

- Uses SDN named-table syntax with `|field|` header
- All rows must have same column count
- Types inferred from literals
- Produces `Table<{id: Int, age: Float, city: Str}>`

### 4.2 Column-Oriented DataFrame Literal

```simple
# Indentation style
val users = dataframe:
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]

# Brace style
val users = dataframe {
    id:   [1, 2, 3]
    age:  [31.0, 24.0, 28.0]
    city: ["Seoul", "Busan", "Seoul"]
}
```

---

### 4.3 External Sources

```simple
val data = read_csv("users.csv")
val json_data = read_json("data.json")
```

- Schema inferred or provided
- Execution deferred until materialization

---

## 5. Table Query Language (tql)

### 5.1 TQL Block Syntax

TQL supports three forms:

```simple
# Form 1: Standalone with 'from' statement
val adults = tql:
    from users
    select @id, @age
    where @age >= 18

val adults = tql {
    from users
    select @id, @age
    where @age >= 18
}

# Form 2: Method chain on table
val adults = users.tql:
    select @id, @age
    where @age >= 18

val adults = users.tql {
    select @id, @age
    where @age >= 18
}
```

Properties:

- Parsed at compile time
- Schema validated statically
- Produces a new `Table<...>`
- No runtime interpretation
- Uses `@` prefix for column references

---

### 5.2 TQL Grammar (LL(1)-Friendly)

```
TqlBlock
  := "tql" Block
  |  Expr ".tql" Block

TqlStatements
  := FromStmt? TqlStmt+

FromStmt    := "from" Expr NEWLINE

TqlStmt
  := SelectStmt
   | WhereStmt
   | GroupByStmt
   | OrderByStmt
   | LimitStmt
   | JoinStmt
   | AggStmt

SelectStmt  := "select" ColumnList NEWLINE
             | "select" "*" NEWLINE

WhereStmt   := "where" BoolExpr NEWLINE

GroupByStmt := "groupby" ColumnList NEWLINE

OrderByStmt := "orderby" ColumnList ("asc" | "desc")? NEWLINE

LimitStmt   := "limit" IntLiteral NEWLINE

JoinStmt    := "join" Expr "on" BoolExpr NEWLINE

AggStmt     := "agg" Block

AggBinding  := IDENT ":" AggExpr NEWLINE

ColumnRef   := "@" IDENT
             | "@" IDENT "." IDENT    # For joins: @users.id
ColumnList  := ColumnRef ("," ColumnRef)*
```

Each statement starts with a distinct keyword, allowing one-pass parsing.

---

### 5.3 Column Resolution Rules

Inside `tql` blocks:

- Column references use `@` prefix: `@age`, `@city`
- Qualified columns for joins: `@users.id`, `@orders.total`
- Outer variables accessed without prefix
- No mutation or assignment

```simple
val threshold = 25
val adults = tql {
    from users
    where @age > threshold  # @age = column, threshold = variable
}
```

---

### 5.4 Expression Subset

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
   | FunctionCall
```

All column expressions are vectorized.

---

## 6. Statistics & Analytics

### 6.1 Descriptive Statistics

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

### 6.4 Predictive Analytics

| Function | Signature | Description |
|----------|-----------|-------------|
| `trend(col)` | `(@Col) -> f64` | Linear trend slope |
| `regress(y, x)` | `(@Col, @Col) -> Regression` | Simple linear regression |
| `ewma(col, alpha)` | `(@Col, f64) -> Column<f64>` | Exponential weighted MA |
| `predict(col, window)` | `(@Col, u64) -> f64` | Simple prediction |
| `anomaly(col)` | `(@Col) -> Column<Bool>` | Anomaly detection (IQR) |

---

### 6.5 Statistics Usage Example

```simple
# Brace style
val city_stats = tql {
    from users
    groupby @city
    agg {
        n: count()
        avg_age: mean(@age)
        std_age: std(@age)
        slope: trend(@age)
        q95: quantile(@age, 0.95)
    }
}

# Indent style
val city_stats = tql:
    from users
    groupby @city
    agg:
        n: count()
        avg_age: mean(@age)
        std_age: std(@age)
        slope: trend(@age)
        q95: quantile(@age, 0.95)

# Method chain style
val city_stats = users.tql {
    groupby @city
    agg {
        n: count()
        avg_age: mean(@age)
    }
}
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

## 7. Other Custom Blocks

The unified block syntax extends to other domain-specific languages:

### 7.1 Math Block

Compile-time mathematical expressions with symbolic computation:

```simple
# Symbolic math expressions
val formula = math {
    f(x) = x^2 + 2*x + 1
    g(x) = sin(x) + cos(x)
    h = f(g(pi/4))
}

val derivative = math:
    d/dx (x^3 + 2*x^2)    # Returns 3*x^2 + 4*x

# Matrix operations
val result = math {
    A = [[1, 2], [3, 4]]
    B = [[5, 6], [7, 8]]
    C = A * B + transpose(A)
}

# Inline math expression
val area = math { pi * r^2 }
```

**Math Block Grammar:**

```
MathBlock := "math" Block

MathStmt
  := Assignment
   | Expression

Assignment := IDENT "=" MathExpr
           |  IDENT "(" ParamList ")" "=" MathExpr

MathExpr
  := MathExpr ("+" | "-" | "*" | "/" | "^") MathExpr
   | FunctionCall
   | Matrix
   | IDENT
   | NUMBER
   | "(" MathExpr ")"
   | DerivativeExpr
   | IntegralExpr

DerivativeExpr := "d" "/" "d" IDENT MathExpr
IntegralExpr   := "integrate" MathExpr "d" IDENT
```

---

### 7.2 Regex Block

Compile-time regex with named captures and validation:

```simple
# Define regex pattern
val email_pattern = regex {
    ^
    (?<user>[a-zA-Z0-9._%+-]+)
    @
    (?<domain>[a-zA-Z0-9.-]+)
    \.
    (?<tld>[a-zA-Z]{2,})
    $
}

# Usage
val matches = email_pattern.match("user@example.com")
val user = matches.get("user")  # Type-safe named capture

# Inline regex
val is_valid = regex { ^\d{3}-\d{4}$ }.test(phone)
```

---

### 7.3 HTML Block

Type-safe HTML generation with compile-time validation:

```simple
val page = html {
    doctype html
    html lang="en" {
        head {
            title { "My Page" }
            meta charset="utf-8"
        }
        body {
            div class="container" {
                h1 { "Hello, " + username }
                p { "Welcome to the site." }
                ul {
                    for item in items {
                        li { item.name }
                    }
                }
            }
        }
    }
}

# Indent style
val card = html:
    div class="card":
        h2: title
        p: description
```

---

### 7.4 CSS Block

Type-safe CSS with compile-time validation:

```simple
val styles = css {
    .container {
        display: flex
        justify-content: center
        padding: 20px
    }

    .card {
        background: #fff
        border-radius: 8px
        box-shadow: 0 2px 4px rgba(0,0,0,0.1)

        &:hover {
            transform: scale(1.02)
        }
    }
}

# Scoped styles
val button_style = css {
    background: $primary_color    # Variable interpolation
    padding: 10px 20px
    border: none
    cursor: pointer
}
```

---

### 7.5 JSON Block

Type-safe JSON with schema validation:

```simple
val config = json {
    "name": "my-app",
    "version": "1.0.0",
    "dependencies": {
        "simple-core": "^2.0",
        "simple-web": "^1.5"
    },
    "settings": {
        "debug": true,
        "port": 8080
    }
}

# With schema validation
val user_data = json<UserSchema> {
    "id": 123,
    "name": "Alice",
    "email": "alice@example.com"
}
```

---

### 7.6 SQL Block (Raw SQL Escape Hatch)

For cases where TQL is insufficient:

```simple
val result = sql {
    SELECT u.name, COUNT(o.id) as order_count
    FROM users u
    LEFT JOIN orders o ON u.id = o.user_id
    WHERE u.created_at > $cutoff_date
    GROUP BY u.id
    HAVING COUNT(o.id) > 5
}
```

---

### 7.7 GraphQL Block

```simple
val query = graphql {
    query GetUser($id: ID!) {
        user(id: $id) {
            name
            email
            posts {
                title
                createdAt
            }
        }
    }
}

val result = api.execute(query, {id: user_id})
```

---

## 8. Execution Model

### 8.1 Lazy Semantics

`tql` blocks construct a logical plan.

Execution is triggered by:

- `print(result)`
- `result.collect()`
- Output operations

---

### 8.2 Logical Plan Nodes

```simple
enum LogicalPlan:
    Scan(source: Table)
    Filter(pred: Predicate, input: Box<LogicalPlan>)
    Project(cols: [Str], input: Box<LogicalPlan>)
    GroupBy(groups: [Str], aggs: [Aggregation], input: Box<LogicalPlan>)
    Join(left: Box<LogicalPlan>, right: Box<LogicalPlan>, on: Predicate)
    Sort(cols: [Str], desc: Bool, input: Box<LogicalPlan>)
    Limit(n: u64, input: Box<LogicalPlan>)
```

Statistics compile into aggregation kernels.

---

## 9. Backend Architecture

### 9.1 Backend Abstraction

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

### 9.2 CUDA Backend

CUDA backend may leverage:

- Column-oriented GPU memory layout
- Parallel reduction kernels
- Thrust-style algorithms
- cuBLAS for linear algebra operations

Statistics are implemented as compiled kernel graphs, not library calls.

---

## 10. GPU Capability & Fallback

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

## 11. Memory Model

- Columnar buffers
- Explicit CPU <-> GPU transfer nodes
- No implicit synchronization
- Arrow-compatible layout

---

## 12. Determinism Guarantees

Custom blocks guarantee:

- Deterministic execution
- No hidden randomness
- No mutable state
- Stable output types

This enables:

- Formal reasoning
- Cost modeling
- Future verification

---

## 13. Summary

| Component | Description |
|-----------|-------------|
| Unified Blocks | `{}` and `:` styles share common interface |
| SDN Table | Row-oriented data interchange format |
| DataFrame | Column-oriented analytics type |
| `tql` | Static query + analytics DSL |
| `math` | Symbolic math and matrix operations |
| `regex` | Compile-time regex patterns |
| `html`/`css` | Type-safe web markup |
| `json` | Schema-validated JSON |
| Statistics | Deterministic aggregation kernels |
| CUDA | Explicit, composable GPU support |

This design keeps Simple fast, analyzable, and compiler-driven.

---

## Related Documents

- `doc/research/statistics_library.md` - Research findings
- `doc/plan/statistics_library_implementation.md` - Implementation plan
- `doc/guide/custom_blocks_quick_reference.md` - Custom block API quick reference
- `simple/std_lib/test/features/stats/table_statistics_spec.spl` - Test specification
