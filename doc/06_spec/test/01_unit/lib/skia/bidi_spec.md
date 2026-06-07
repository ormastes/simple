# Bidi Specification

> <details>

<!-- sdn-diagram:id=bidi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bidi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bidi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bidi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidi Specification

## Scenarios

### classify_bidi: character class detection

#### ASCII 'A' (U+0041 = 65) returns L

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cls = classify_bidi(65)
expect cls to_equal BidiClass.L
```

</details>

#### Hebrew alef (U+05D0 = 1488) returns R

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cls = classify_bidi(1488)
expect cls to_equal BidiClass.R
```

</details>

#### Arabic alif (U+0627 = 1575) returns AL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cls = classify_bidi(1575)
expect cls to_equal BidiClass.AL
```

</details>

#### ASCII digit '0' (U+0030 = 48) returns EN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cls = classify_bidi(48)
expect cls to_equal BidiClass.EN
```

</details>

#### ASCII space (U+0020 = 32) returns ON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cls = classify_bidi(32)
expect cls to_equal BidiClass.ON
```

</details>

### is_rtl: primary direction detection

#### sequence starting with Latin 'A' returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps: [i64] = [65, 66, 67]
val result = is_rtl(cps)
expect result to_equal false
```

</details>

#### sequence starting with Hebrew alef (1488) returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps: [i64] = [1488, 1489, 1490]
val result = is_rtl(cps)
expect result to_equal true
```

</details>

### compute_embedding_levels: pure LTR text

#### pure ASCII Latin text with base LTR produces all level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'A'=65, 'B'=66, 'C'=67
val cps: [i64] = [65, 66, 67]
val levels = compute_embedding_levels(cps, false)
val l0 = levels[0]
val l1 = levels[1]
val l2 = levels[2]
expect l0 to_equal 0
expect l1 to_equal 0
expect l2 to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/bidi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- classify_bidi: character class detection
- is_rtl: primary direction detection
- compute_embedding_levels: pure LTR text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
