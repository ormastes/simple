# Strings Specification

> <details>

<!-- sdn-diagram:id=strings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=strings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

strings_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=strings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strings Specification

## Scenarios

### strings tool

#### printable detection

#### identifies printable ASCII range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 65  # 'A'
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(true)
```

</details>

#### rejects control characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 0
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(false)
```

</details>

#### minimum length

#### filters short strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "ab"
val min_len = 4
expect(s.len() < min_len).to_equal(true)
```

</details>

#### keeps long enough strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val min_len = 4
expect(s.len() >= min_len).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/strings_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- strings tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
