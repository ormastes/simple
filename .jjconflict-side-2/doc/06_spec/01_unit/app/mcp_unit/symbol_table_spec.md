# Symbol Table Specification

> <details>

<!-- sdn-diagram:id=symbol_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_table_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Specification

## Scenarios

### extract_json_string for symbol data

#### extracts symbol name from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("name", js("MyClass")), jp("kind", js("class")))
expect(extract_json_string(json, "name")).to_equal("MyClass")
```

</details>

#### extracts symbol kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("name", js("helper")), jp("kind", js("function")))
expect(extract_json_string(json, "kind")).to_equal("function")
```

</details>

#### extracts module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("module", js("mcp.simple_lang")))
expect(extract_json_string(json, "module")).to_equal("mcp.simple_lang")
```

</details>

#### returns empty for missing symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("name", js("test")))
expect(extract_json_string(json, "kind")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/symbol_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_json_string for symbol data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
