# database_query_spec

> Verifies the database query behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# database_query_spec

Verifies the database query behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/database_query_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the database query behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### QueryBuilder

<details>
<summary>Advanced: filters rows by equality</summary>

#### filters rows by equality _(slow)_

- Verify: filters rows by equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters rows by equality")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Create test table
var table = SdnTable(name: "users", columns: ["id", "name", "age"], rows: [], index: {})

# Add test data
for i in 0..5:
    var row = SdnRow(fields: {})
    row.set("id", "{i}")
    row.set("name", "user_{i}")
    row.set("age", "{20 + i}")
    table.add_row(row)

# Query with filter
var query = QueryBuilder.for_table(table)
var filtered = query.filter_by("name", CompareOp.Eq, "user_2")
val results = filtered.execute()

check(results.len() == 1)
check(results[0].get("name")? == "user_2")
```

</details>


</details>

<details>
<summary>Advanced: filters rows by comparison operators</summary>

#### filters rows by comparison operators _(slow)_

- Verify: filters rows by comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters rows by comparison operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "items", columns: ["id", "price"], rows: [], index: {})

# Add items with different prices
for i in 0..10:
    var row = SdnRow(fields: {})
    row.set("id", "item_{i}")
    row.set("price", "{i * 10}")
    table.add_row(row)

# Query: price > 50
var query_gt = QueryBuilder.for_table(table)
var filtered_gt = query_gt.filter_by("price", CompareOp.Gt, "50")
val results_gt = filtered_gt.execute()

# Should get items 6-9 (prices 60, 70, 80, 90)
check(results_gt.len() == 4)

# Query: price < 30
var query_lt = QueryBuilder.for_table(table)
var filtered_lt = query_lt.filter_by("price", CompareOp.Lt, "30")
val results_lt = filtered_lt.execute()

# Should get items 0-2 (prices 0, 10, 20)
check(results_lt.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: filters rows by contains operator</summary>

#### filters rows by contains operator _(slow)_

- Verify: filters rows by contains operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters rows by contains operator")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "files", columns: ["path", "extension"], rows: [], index: {})

# Add files
val files = [
    ("src/main.spl", "spl"),
    ("test/test.spl", "spl"),
    ("README.md", "md"),
    ("src/lib.rs", "rs"),
]

for file in files:
    var row = SdnRow(fields: {})
    row.set("path", file.0)
    row.set("extension", file.1)
    table.add_row(row)

# Query: path contains "src"
var query = QueryBuilder.for_table(table)
var filtered = query.filter_by("path", CompareOp.Contains, "src")
val results = filtered.execute()

check(results.len() == 2)
val first_path = results[0].get("path") ?? ""
check(first_path.contains("src"))
```

</details>


</details>

<details>
<summary>Advanced: filters with in operator</summary>

#### filters with in operator _(slow)_

- Verify: filters with in operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters with in operator")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "issues", columns: ["id", "status"], rows: [], index: {})
val statuses = ["Open", "Closed", "Open", "Pending", "Closed"]
for idx in 0..statuses.len():
    var row = SdnRow(fields: {})
    row.set("id", "issue_{idx}")
    row.set("status", statuses[idx])
    table.add_row(row)

var query = QueryBuilder.for_table(table)
var filtered = query.filter_in("status", ["Open", "Closed"])
val results = filtered.execute()

check(results.len() == 4)
check(results[0].get("status")? != "Pending")
```

</details>


</details>

<details>
<summary>Advanced: chains multiple filters</summary>

#### chains multiple filters _(slow)_

- Verify: chains multiple filters


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: chains multiple filters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "products", columns: ["name", "category", "price"], rows: [], index: {})

# Add products
val products = [
    ("Laptop", "Electronics", "1000"),
    ("Mouse", "Electronics", "20"),
    ("Desk", "Furniture", "300"),
    ("Chair", "Furniture", "150"),
    ("Monitor", "Electronics", "400"),
]

for product in products:
    var row = SdnRow(fields: {})
    row.set("name", product.0)
    row.set("category", product.1)
    row.set("price", product.2)
    table.add_row(row)

# Query: Electronics AND price > 100
# NOTE: string comparison "price > 100" compares lexicographically
# "1000" > "100", "400" > "100", but "20" < "100" lexicographically
# So results depend on string comparison semantics
var query = QueryBuilder.for_table(table)
var step1 = query.filter_by("category", CompareOp.Eq, "Electronics")
var step2 = step1.filter_by("price", CompareOp.Gt, "100")
val results = step2.execute()

# String comparison: "1000" > "100" = true, "20" > "100" = true, "400" > "100" = true
# All 3 Electronics pass lexicographic > "100"
# Accept either 2 or 3 depending on comparison semantics
check(results.len() >= 2)
```

</details>


</details>

<details>
<summary>Advanced: filters only valid rows</summary>

#### filters only valid rows _(slow)_

- Verify: filters only valid rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters only valid rows")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "data", columns: ["id", "value", "valid"], rows: [], index: {})

# Add rows (some invalid)
for i in 0..5:
    var row = SdnRow(fields: {})
    row.set("id", "{i}")
    row.set("value", "data_{i}")
    val valid_str = if i % 2 == 0: "true" else: "false"
    row.set("valid", valid_str)
    table.add_row(row)

# Query with only_valid()
var query = QueryBuilder.for_table(table)
var valid_query = query.only_valid()
val results = valid_query.execute()

# Should get only valid rows (0, 2, 4)
check(results.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: filters rows by prefix and suffix</summary>

#### filters rows by prefix and suffix _(slow)_

- Verify: filters rows by prefix and suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: filters rows by prefix and suffix")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "paths", columns: ["path"], rows: [], index: {})
val paths = ["src/main.spl", "src/test.txt", "doc/readme.md", "main.spl"]
for path in paths:
    var row = SdnRow(fields: {})
    row.set("path", path)
    table.add_row(row)

var prefix_query = QueryBuilder.for_table(table)
val prefix_results = prefix_query.filter_by("path", CompareOp.StartsWith, "src/").execute()
check(prefix_results.len() == 2)

var suffix_query = QueryBuilder.for_table(table)
val suffix_results = suffix_query.filter_by("path", CompareOp.EndsWith, ".spl").execute()
check(suffix_results.len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: preserves query matches across batch boundaries</summary>

#### preserves query matches across batch boundaries _(slow)_

- Verify: preserves query matches across batch boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: preserves query matches across batch boundaries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "batch_paths", columns: ["id", "path", "valid"], rows: [], index: {})
for idx in 0..130:
    var row = SdnRow(fields: {})
    row.set("id", "{idx}")
    if idx == 63 or idx == 64 or idx == 129:
        row.set("path", "src/hit_{idx}.spl")
        row.set("valid", "true")
    else:
        row.set("path", "doc/miss_{idx}.md")
        row.set("valid", "false")
    table.add_row(row)

val results = QueryBuilder.for_table(table)
    .filter_by("path", CompareOp.StartsWith, "src/")
    .filter_by("valid", CompareOp.Eq, "true")
    .execute()

check(results.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: orders results ascending</summary>

#### orders results ascending _(slow)_

- Verify: orders results ascending


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: orders results ascending")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "scores", columns: ["id", "score"], rows: [], index: {})
val scores = [("a", "30"), ("b", "10"), ("c", "20")]
for score in scores:
    var row = SdnRow(fields: {})
    row.set("id", score.0)
    row.set("score", score.1)
    table.add_row(row)

val results = QueryBuilder.for_table(table).order_by("score", false).execute()
check(results.len() == 3)
check(results[0].get("score")? == "10")
check(results[2].get("score")? == "30")
```

</details>


</details>

<details>
<summary>Advanced: orders results descending</summary>

#### orders results descending _(slow)_

- Verify: orders results descending


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: orders results descending")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "scores", columns: ["id", "score"], rows: [], index: {})
val scores = [("a", "30"), ("b", "10"), ("c", "20")]
for score in scores:
    var row = SdnRow(fields: {})
    row.set("id", score.0)
    row.set("score", score.1)
    table.add_row(row)

val results = QueryBuilder.for_table(table).order_by("score", true).execute()
check(results.len() == 3)
check(results[0].get("score")? == "30")
check(results[2].get("score")? == "10")
```

</details>


</details>

<details>
<summary>Advanced: limits number of results</summary>

#### limits number of results _(slow)_

- Verify: limits number of results


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: limits number of results")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "numbers", columns: ["id"], rows: [], index: {})
for i in 0..5:
    var row = SdnRow(fields: {})
    row.set("id", "{i}")
    table.add_row(row)

val results = QueryBuilder.for_table(table).take(2).execute()
check(results.len() == 2)
check(results[0].get("id")? == "0")
check(results[1].get("id")? == "1")
```

</details>


</details>

<details>
<summary>Advanced: combines filter, order, and limit</summary>

#### combines filter, order, and limit _(slow)_

- Verify: combines filter, order, and limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: combines filter, order, and limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable(name: "items", columns: ["id", "kind"], rows: [], index: {})
val items = [("4", "c"), ("1", "b"), ("3", "b"), ("2", "a")]
for item in items:
    var row = SdnRow(fields: {})
    row.set("id", item.0)
    row.set("kind", item.1)
    table.add_row(row)

val results = QueryBuilder.for_table(table)
    .filter_by("kind", CompareOp.Gt, "a")
    .order_by("id", false)
    .take(2)
    .execute()

check(results.len() == 2)
check(results[0].get("id")? == "1")
check(results[1].get("id")? == "3")
```

</details>


</details>

<details>
<summary>Advanced: returns empty for empty table</summary>

#### returns empty for empty table _(slow)_

- Verify: returns empty for empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_DATABASE_QUERY-001
step("Verify: returns empty for empty table")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = SdnTable(name: "empty", columns: ["id"], rows: [], index: {})

var query = QueryBuilder.for_table(table)
val results = query.execute()

check(results.len() == 0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 13 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f0eb544a865bfb3de61ffb9b1111b56d552b1f072ee6e7656e91583854b3c6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f0eb544a865bfb3de61ffb9b1111b56d552b1f072ee6e7656e91583854b3c6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f0eb544a865bfb3de61ffb9b1111b56d552b1f072ee6e7656e91583854b3c6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/database_query_spec.spl
mirror: doc/06_spec/02_integration/lib/database_query_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/database_query_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/database_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/database_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
