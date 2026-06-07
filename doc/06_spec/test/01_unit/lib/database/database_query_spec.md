# Database Query Specification

> 1. [

<!-- sdn-diagram:id=database_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_query_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Query Specification

## Scenarios

### Database Query — shared accel batching

#### keeps filter_in as OR semantics

1. [

2. [

3. [

4. [

5.  filter in

6.  execute
   - Expected: results.len() equals `3`
   - Expected: results[0].get("status")? equals `Open`
   - Expected: results[1].get("status")? equals `Closed`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("issues", ["id", "status"], [
    [("id", "1"), ("status", "Open")],
    [("id", "2"), ("status", "Closed")],
    [("id", "3"), ("status", "Pending")],
    [("id", "4"), ("status", "Open")]
])

val results = QueryBuilder.for_table(table)
    .filter_in("status", ["Open", "Closed"])
    .execute()

expect(results.len()).to_equal(3)
expect(results[0].get("status")?).to_equal("Open")
expect(results[1].get("status")?).to_equal("Closed")
```

</details>

#### supports shared prefix and suffix filtering

1. [

2. [

3. [

4. [

5. [

6.  filter by

7.  execute

8.  filter by

9.  execute
   - Expected: prefix_results.len() equals `3`
   - Expected: prefix_results[0].get("path")? equals `src/zeta.spl`
   - Expected: prefix_results[1].get("path")? equals `src/lib.rs`
   - Expected: suffix_results.len() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("paths", ["path"], [
    [("path", "src/zeta.spl")],
    [("path", "src/lib.rs")],
    [("path", "doc/readme.md")],
    [("path", "main.spl")],
    [("path", "src/alpha.spl")]
])

val prefix_results = QueryBuilder.for_table(table)
    .filter_by("path", CompareOp.StartsWith, "src/")
    .execute()
val suffix_results = QueryBuilder.for_table(table)
    .filter_by("path", CompareOp.EndsWith, ".spl")
    .execute()

expect(prefix_results.len()).to_equal(3)
expect(prefix_results[0].get("path")?).to_equal("src/zeta.spl")
expect(prefix_results[1].get("path")?).to_equal("src/lib.rs")
expect(suffix_results.len()).to_equal(3)
```

</details>

#### reuses a field prefix index across repeated StartsWith executions

1. [

2. [

3. [

4. var query = QueryBuilder for table

5.  filter by
   - Expected: first.len() equals `2`
   - Expected: second.len() equals `2`
   - Expected: first_builds equals `1`
   - Expected: second_builds equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("paths", ["path"], [
    [("path", "src/a.spl")],
    [("path", "src/b.spl")],
    [("path", "doc/readme.md")]
])
var query = QueryBuilder.for_table(table)
    .filter_by("path", CompareOp.StartsWith, "src/")

val first = query.execute()
val first_builds = query.prefix_index_build_count()
val second = query.execute()
val second_builds = query.prefix_index_build_count()

expect(first.len()).to_equal(2)
expect(second.len()).to_equal(2)
expect(first_builds).to_equal(1)
expect(second_builds).to_equal(1)
```

</details>

#### sorts ascending and descending without optional-field interpreter gaps

1. [

2. [

3. [
   - Expected: asc[0].get("score")? equals `10`
   - Expected: asc[2].get("score")? equals `30`
   - Expected: desc[0].get("score")? equals `30`
   - Expected: desc[2].get("score")? equals `10`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("scores", ["id", "score"], [
    [("id", "a"), ("score", "30")],
    [("id", "b"), ("score", "10")],
    [("id", "c"), ("score", "20")]
])

val asc = QueryBuilder.for_table(table).order_by("score", false).execute()
val desc = QueryBuilder.for_table(table).order_by("score", true).execute()

expect(asc[0].get("score")?).to_equal("10")
expect(asc[2].get("score")?).to_equal("30")
expect(desc[0].get("score")?).to_equal("30")
expect(desc[2].get("score")?).to_equal("10")
```

</details>

#### applies limit after filtering and sorting

1. [

2. [

3. [

4. [

5.  filter by

6.  order by

7.  take

8.  execute
   - Expected: results.len() equals `2`
   - Expected: results[0].get("id")? equals `1`
   - Expected: results[1].get("id")? equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("items", ["id", "kind"], [
    [("id", "1"), ("kind", "b")],
    [("id", "2"), ("kind", "a")],
    [("id", "3"), ("kind", "b")],
    [("id", "4"), ("kind", "c")]
])

val results = QueryBuilder.for_table(table)
    .filter_by("kind", CompareOp.Gt, "a")
    .order_by("id", false)
    .take(2)
    .execute()

expect(results.len()).to_equal(2)
expect(results[0].get("id")?).to_equal("1")
expect(results[1].get("id")?).to_equal("3")
```

</details>

#### keeps execute_bitmap semantics across chained filters

1. [

2. [

3. [

4. [

5. [

6.  filter by

7.  filter in

8.  filter by
   - Expected: bitmap.count() equals `3`
   - Expected: bitmap.get(0) is true
   - Expected: bitmap.get(1) is true
   - Expected: bitmap.get(2) is false
   - Expected: bitmap.get(3) is true
   - Expected: bitmap.get(4) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = make_table("files", ["id", "path", "kind", "status"], [
    [("id", "1"), ("path", "src/main.spl"), ("kind", "code"), ("status", "Open")],
    [("id", "2"), ("path", "src/lib.rs"), ("kind", "code"), ("status", "Closed")],
    [("id", "3"), ("path", "doc/readme.md"), ("kind", "doc"), ("status", "Open")],
    [("id", "4"), ("path", "src/query.spl"), ("kind", "code"), ("status", "Open")],
    [("id", "5"), ("path", "src/query.txt"), ("kind", "doc"), ("status", "Open")]
])

val builder = QueryBuilder.for_table(table)
    .filter_by("path", CompareOp.StartsWith, "src/")
    .filter_in("status", ["Open", "Closed"])
    .filter_by("kind", CompareOp.Eq, "code")
val bitmap = builder.execute_bitmap()

expect(bitmap.count()).to_equal(3)
expect(bitmap.get(0)).to_equal(true)
expect(bitmap.get(1)).to_equal(true)
expect(bitmap.get(2)).to_equal(false)
expect(bitmap.get(3)).to_equal(true)
expect(bitmap.get(4)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Database Query — shared accel batching

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
