# Char Code Specification

> <details>

<!-- sdn-diagram:id=char_code_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=char_code_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

char_code_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=char_code_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Char Code Specification

## Scenarios

### text.from_char_code interpreter support

#### converts ASCII letter codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = text.from_char_code(65)
expect(a).to_equal("A")
val z = text.from_char_code(90)
expect(z).to_equal("Z")
```

</details>

#### converts lowercase letter codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = text.from_char_code(97)
expect(a).to_equal("a")
```

</details>

#### converts digit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = text.from_char_code(48)
expect(zero).to_equal("0")
```

</details>

#### converts space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = text.from_char_code(32)
expect(sp).to_equal(" ")
```

</details>

#### handles null char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val null_ch = text.from_char_code(0)
expect(null_ch.len()).to_equal(1)
```

</details>

#### converts tilde

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tilde = text.from_char_code(126)
expect(tilde).to_equal("~")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/debug/formats/char_code_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text.from_char_code interpreter support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
