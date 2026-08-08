# Query Visibility Specification

> <details>

<!-- sdn-diagram:id=query_visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_visibility_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Specification

## Scenarios

### query_visibility module path normalization

#### maps bare type imports to default type domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "Text"
val type_base = "src/type/simple_lang/" + mod_path
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/Text.spl")
```

</details>

#### maps owned-domain type imports to underscore directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "simple-lang/Bool"
val slash_parts = mod_path.split("/")
val type_base = "type/" + slash_parts[0].replace("-", "_") + "/" + slash_parts[1..].join("/")
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/Bool.spl")
```

</details>

#### keeps std imports on lib path

1. path = "lib " + path substring
   - Expected: file_base equals `src/lib/text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var path = "std.text"
if path.starts_with("std."):
    path = "lib." + path.substring(4)
val file_base = "src/" + path.split(".").join("/")
expect(file_base).to_equal("src/lib/text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query_visibility module path normalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
