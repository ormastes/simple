# Core Interner Table Specification

> <details>

<!-- sdn-diagram:id=core_interner_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_interner_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_interner_table_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_interner_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Core Interner Table Specification

## Scenarios

### Core Ext

#### keeps string interner and row primitives available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = database_core_source()

expect(source).to_contain("class StringInterner:")
expect(source).to_contain("me intern(s: text) -> i32")
expect(source).to_contain("fn lookup(id: i32) -> text?")
expect(source).to_contain("struct SdnRow:")
expect(source).to_contain("fn get_bool(column: text) -> bool?")
expect(source).to_contain("me set(column: text, value: text)")
```

</details>

#### keeps SDN table parsing and valid row behavior available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = database_core_source()

expect(source).to_contain("class SdnTable:")
expect(source).to_contain("static fn parse(content: text) -> SdnTable?")
expect(source).to_contain("fn to_sdn() -> text")
expect(source).to_contain("me mark_deleted(key: text) -> bool")
expect(source).to_contain("fn valid_rows() -> [SdnRow]")
expect(source).to_contain("fn split_sdn_row(line: text) -> [text]")
```

</details>

#### keeps SDN database persistence and wrappers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = database_core_source()

expect(source).to_contain("class SdnDatabase:")
expect(source).to_contain("static fn load(path: text) -> SdnDatabase?")
expect(source).to_contain("me save() -> bool")
expect(source).to_contain("me add_row_to_table(table_name: text, row: SdnRow) -> bool")
expect(source).to_contain("fn validate() -> [text]")
expect(source).to_contain("fn load_sdn_database(path: text) -> SdnDatabase?")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/core_interner_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Core Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
