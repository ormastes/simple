# String Core Specification

> <details>

<!-- sdn-diagram:id=string_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Specification

## Scenarios

### String Core

#### keeps character access and ASCII conversion helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = string_core_source()

expect(source).to_contain("fn str_char_at(s: text, idx: i64) -> text")
expect(source).to_contain("fn char_code(c: text) -> i64")
expect(source).to_contain("fn char_from_code(code: i64) -> text")
expect(source).to_contain("code >= 32 and code <= 126")
```

</details>

#### keeps bounded repeat construction available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = string_core_source()

expect(source).to_contain("fn str_repeat(s: text, count: i64) -> text")
expect(source).to_contain("if count <= 0:")
expect(source).to_contain("parts.push(s)")
expect(source).to_contain("parts.join(\"\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- String Core

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
