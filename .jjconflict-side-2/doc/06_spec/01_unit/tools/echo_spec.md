# Echo Specification

> <details>

<!-- sdn-diagram:id=echo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=echo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

echo_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=echo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Echo Specification

## Scenarios

### echo tool

#### escape processing

#### processes newline escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_escapes("hello\\nworld")
expect(result).to_equal("hello\nworld")
```

</details>

#### processes tab escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_escapes("col1\\tcol2")
expect(result).to_equal("col1\tcol2")
```

</details>

#### processes backslash escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_escapes("back\\\\slash")
expect(result).to_equal("back\\slash")
```

</details>

#### leaves non-escape text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_escapes("hello world")
expect(result).to_equal("hello world")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_escapes("")
expect(result).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/echo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- echo tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
