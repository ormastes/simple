# T32 Cli Catalog Specification

> <details>

<!-- sdn-diagram:id=t32_cli_catalog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_catalog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_catalog_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_catalog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Catalog Specification

## Scenarios

### T32 Catalog Loader (real SDN files)

#### windows.sdn

#### loads window entries from real catalog file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 11 windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
expect(entries.len()).to_be_greater_than(10)
```

</details>

#### contains break_list window

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "break_list":
        found = true
        expect(e["title"] ?? "").to_equal("Breakpoint List")
        expect(e["kind"] ?? "").to_equal("built_in")
expect(found).to_equal(true)
```

</details>

#### contains register_view window

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "register_view":
        found = true
        expect(e["title"] ?? "").to_equal("CPU Registers")
expect(found).to_equal(true)
```

</details>

#### each window has open_command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
for e in entries:
    val open_cmd = e["open_command"] ?? ""
    expect(open_cmd.len()).to_be_greater_than(0)
```

</details>

#### actions.sdn

#### loads action entries from real catalog file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 10 actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
expect(entries.len()).to_be_greater_than(9)
```

</details>

#### contains set_break action with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "set_break":
        found = true
        expect(e["label"] ?? "").to_equal("Set Breakpoint")
        expect(e["type"] ?? "").to_equal("execute")
expect(found).to_equal(true)
```

</details>

#### fields.sdn

#### loads field entries from real catalog file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 10 fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
expect(entries.len()).to_be_greater_than(9)
```

</details>

#### contains symbol field with correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "symbol":
        found = true
        expect(e["label"] ?? "").to_equal("Symbol Name")
        expect(e["type"] ?? "").to_equal("string")
        expect(e["scope"] ?? "").to_equal("window")
expect(found).to_equal(true)
```

</details>

#### lookup by key

#### finds window by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found_title = ""
for e in entries:
    if (e["_key"] ?? "") == "trace_list":
        found_title = e["title"] ?? ""
expect(found_title).to_equal("Trace List")
```

</details>

#### finds action by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
var found_label = ""
for e in entries:
    if (e["_key"] ?? "") == "go":
        found_label = e["label"] ?? ""
expect(found_label).to_equal("Resume Execution")
```

</details>

#### finds field by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
var found_label = ""
for e in entries:
    if (e["_key"] ?? "") == "elf_path":
        found_label = e["label"] ?? ""
expect(found_label).to_equal("ELF Binary Path")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_catalog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Catalog Loader (real SDN files)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
