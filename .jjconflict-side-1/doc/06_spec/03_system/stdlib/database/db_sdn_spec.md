# Database SDN Table Import/Export

> Simple DB supports reading and writing table data as SDN named tables. The SDN file is human-readable and uses the table's column names as fields.

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database SDN Table Import/Export

Simple DB supports reading and writing table data as SDN named tables. The SDN file is human-readable and uses the table's column names as fields.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/database/db_sdn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple DB supports reading and writing table data as SDN named tables.
The SDN file is human-readable and uses the table's column names as fields.

## SDN Format
```sdn
users |id, name, active|
    1, "Alice", true
    2, "Bob", false
```

## Scenarios

### Database SDN table export

#### exports table with simple values to SDN

1. row1 set

2. row1 set

3. row1 set

4. table add row

5. row2 set

6. row2 set

7. row2 set

8. table add row


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable.new("users", ["id", "name", "active"])
val row1 = SdnRow.empty()
row1.set("id", "1")
row1.set("name", "Alice")
row1.set("active", "true")
table.add_row(row1)

val row2 = SdnRow.empty()
row2.set("id", "2")
row2.set("name", "Bob")
row2.set("active", "false")
table.add_row(row2)

val exported = table.to_sdn()
expect(exported).to_contain("users |id, name, active|")
expect(exported).to_contain("Alice")
expect(exported).to_contain("Bob")
```

</details>

#### exports table with quoted values containing commas

1. row set

2. row set

3. table add row


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable.new("data", ["id", "description"])
val row = SdnRow.empty()
row.set("id", "1")
row.set("description", "hello, world")
table.add_row(row)

val exported = table.to_sdn()
expect(exported).to_contain('"hello, world"')
```

</details>

### Database SDN table import

#### imports table from SDN text

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_text = "users |id, name, active|{NL}    1, Alice, true{NL}    2, Bob, false"
val table = SdnTable.parse(sdn_text)
expect(table != nil).to_equal(true)

val t = table.unwrap()
expect(t.name).to_equal("users")
expect(t.columns.len()).to_equal(3)
expect(t.rows.len()).to_equal(2)
```

</details>

#### imports and reads row values

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_text = "users |id, name|{NL}    1, Alice{NL}    2, Bob"
val table = SdnTable.parse(sdn_text)
val t = table.unwrap()
val first_row = t.rows[0]
expect(first_row.get("id")).to_equal(Some("1"))
expect(first_row.get("name")).to_equal(Some("Alice"))
```

</details>

### Database SDN round-trip

#### round-trips simple table through export and import

1. row set

2. row set

3. row set

4. table add row
   - Expected: reimported != nil is true
   - Expected: t.name equals `projects`
   - Expected: t.rows.len() equals `1`
   - Expected: r.get("name") equals `Some("Simple")`
   - Expected: r.get("status") equals `Some("active")`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create table
val table = SdnTable.new("projects", ["id", "name", "status"])
val row = SdnRow.empty()
row.set("id", "1")
row.set("name", "Simple")
row.set("status", "active")
table.add_row(row)

# Export then re-import
val exported = table.to_sdn()
val reimported = SdnTable.parse(exported)
expect(reimported != nil).to_equal(true)

val t = reimported.unwrap()
expect(t.name).to_equal("projects")
expect(t.rows.len()).to_equal(1)
val r = t.rows[0]
expect(r.get("name")).to_equal(Some("Simple"))
expect(r.get("status")).to_equal(Some("active"))
```

</details>

#### round-trips quoted values with commas

1. row set

2. row set

3. table add row
   - Expected: r.get("text") equals `Some("first, second, third")`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable.new("notes", ["id", "text"])
val row = SdnRow.empty()
row.set("id", "1")
row.set("text", "first, second, third")
table.add_row(row)

val exported = table.to_sdn()
val reimported = SdnTable.parse(exported)
val t = reimported.unwrap()
val r = t.rows[0]
expect(r.get("text")).to_equal(Some("first, second, third"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
