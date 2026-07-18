# Catalog Loader Specification

> <details>

<!-- sdn-diagram:id=catalog_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=catalog_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

catalog_loader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=catalog_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Catalog Loader Specification

## Scenarios

### T32 Catalog Loader

#### parses window catalog entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window break_list\n  title: Breakpoint List\n  kind: built_in\n  capture_mode: print_parse"
val entries = parse_sdn_block(sdn, "window")
expect(entries.len()).to_equal(1)
expect(entries[0]["_key"]).to_equal("break_list")
expect(entries[0]["title"]).to_equal("Breakpoint List")
expect(entries[0]["kind"]).to_equal("built_in")
```

</details>

#### parses multiple entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window a\n  title: Window A\n\nwindow b\n  title: Window B"
val entries = parse_sdn_block(sdn, "window")
expect(entries.len()).to_equal(2)
expect(entries[0]["_key"]).to_equal("a")
expect(entries[1]["_key"]).to_equal("b")
```

</details>

#### parses action catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "action set_break\n  label: Set Breakpoint\n  type: execute\n  command: Break.Set"
val entries = parse_sdn_block(sdn, "action")
expect(entries.len()).to_equal(1)
expect(entries[0]["label"]).to_equal("Set Breakpoint")
expect(entries[0]["type"]).to_equal("execute")
```

</details>

#### parses field catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "field symbol\n  label: Symbol Name\n  type: string\n  scope: window"
val entries = parse_sdn_block(sdn, "field")
expect(entries.len()).to_equal(1)
expect(entries[0]["label"]).to_equal("Symbol Name")
expect(entries[0]["scope"]).to_equal("window")
```

</details>

#### skips comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "# This is a comment\nwindow test\n  title: Test Window"
val entries = parse_sdn_block(sdn, "window")
expect(entries.len()).to_equal(1)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = parse_sdn_block("", "window")
expect(entries.len()).to_equal(0)
```

</details>

#### parses entry with many properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window mem\n  title: Memory\n  kind: built_in\n  capture_mode: print_parse\n  open_command: Data.dump\n  capture_command: WinPrint.Data.dump"
val entries = parse_sdn_block(sdn, "window")
expect(entries[0]["open_command"]).to_equal("Data.dump")
expect(entries[0]["capture_command"]).to_equal("WinPrint.Data.dump")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/catalog_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Catalog Loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
