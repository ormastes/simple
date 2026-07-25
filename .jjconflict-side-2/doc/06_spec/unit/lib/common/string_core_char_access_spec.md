# String Core Char Access Specification

> <details>

<!-- sdn-diagram:id=string_core_char_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_char_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_char_access_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_char_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Char Access Specification

## Scenarios

### string core char access

#### returns characters for valid indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("abc", 0)).to_equal("a")
expect(str_char_at("abc", 2)).to_equal("c")
```

</details>

#### returns empty text for invalid indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("abc", -1)).to_equal("")
expect(str_char_at("abc", 3)).to_equal("")
expect(str_char_at("", 0)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/string_core_char_access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- string core char access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
