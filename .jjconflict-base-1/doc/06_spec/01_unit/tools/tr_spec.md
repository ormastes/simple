# Tr Specification

> <details>

<!-- sdn-diagram:id=tr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tr Specification

## Scenarios

### tr tool

#### set expansion

#### expands upper class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = expand_set("[:upper:]")
expect(result).to_equal("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
```

</details>

#### expands lower class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = expand_set("[:lower:]")
expect(result).to_equal("abcdefghijklmnopqrstuvwxyz")
```

</details>

#### expands digit class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = expand_set("[:digit:]")
expect(result).to_equal("0123456789")
```

</details>

#### passes through literal characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = expand_set("abc")
expect(result).to_equal("abc")
```

</details>

#### char code conversion

#### gets code for letter a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_val("a")
expect(code).to_equal(97)
```

</details>

#### gets code for letter A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_val("A")
expect(code).to_equal(65)
```

</details>

#### converts code back to char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = code_to_char(97)
expect(ch).to_equal("a")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/tr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tr tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
