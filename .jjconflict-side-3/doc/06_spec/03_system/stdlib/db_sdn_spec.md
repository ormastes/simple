# Database SDN Table Import/Export

> Simple DB supports reading and writing table data as SDN named tables. This spec uses a small local model to validate the parser-safe behavior of importing and exporting SDN tables.

<!-- sdn-diagram:id=db_sdn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_sdn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_sdn_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_sdn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database SDN Table Import/Export

Simple DB supports reading and writing table data as SDN named tables. This spec uses a small local model to validate the parser-safe behavior of importing and exporting SDN tables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/db_sdn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple DB supports reading and writing table data as SDN named tables.
This spec uses a small local model to validate the parser-safe behavior of
importing and exporting SDN tables.

## SDN Format
```sdn
users |id, name, active|
    1, "Alice", true
    2, "Bob", false
```

## Scenarios

### Database SDN table import/export
_Tests for SDN table import and export functionality._

#### exports users table to SDN

1. var row = SdnTable empty row

2. table add row


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable.new("users", ["id", "name", "active"])
var row = SdnTable.empty_row()
row["id"] = "1"
row["name"] = "Alice"
row["active"] = "true"
table.add_row(row)

val exported = table.to_sdn()
expect(exported).to_contain("users |id, name, active|")
expect(exported).to_contain("Alice")
expect(exported).to_contain("true")
```

</details>

#### imports users table from SDN

1. Some
   - Expected: resolved.name equals `users`
   - Expected: resolved.columns.len() equals `3`
   - Expected: resolved.rows.len() equals `2`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "users |id, name, active|\n    1, \"Alice\", true\n    2, \"Bob\", false"
val table = parse_sdn_table(content)
match table:
    Some(resolved):
        expect(resolved.name).to_equal("users")
        expect(resolved.columns.len()).to_equal(3)
        expect(resolved.rows.len()).to_equal(2)
    nil:
        expect(false).to_equal(true)
```

</details>

#### round-trips quoted values with commas

1. var row = SdnTable empty row

2. table add row

3. Some
   - Expected: resolved.rows.len() equals `1`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable.new("notes", ["id", "description"])
var row = SdnTable.empty_row()
row["id"] = "1"
row["description"] = "hello, world"
table.add_row(row)

val exported = table.to_sdn()
expect(exported).to_contain('"hello, world"')

val parsed = parse_sdn_table(exported)
match parsed:
    Some(resolved):
        expect(resolved.rows.len()).to_equal(1)
    nil:
        expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
