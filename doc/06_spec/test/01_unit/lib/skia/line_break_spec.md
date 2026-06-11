# Skia Text Line-Break Specification

> Tests for find_break_opportunities and wrap_text — the simplified UAX#14 line breaker that mirrors Skia's SkShaper line-break logic for English/Latin scripts.

<!-- sdn-diagram:id=line_break_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=line_break_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

line_break_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=line_break_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Text Line-Break Specification

Tests for find_break_opportunities and wrap_text — the simplified UAX#14 line breaker that mirrors Skia's SkShaper line-break logic for English/Latin scripts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-TEXT-LB-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/line_break_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for find_break_opportunities and wrap_text — the simplified UAX#14
line breaker that mirrors Skia's SkShaper line-break logic for
English/Latin scripts.

Width measurement uses a fixed per-character width (6.0 px) because
passing `fn` callbacks across module boundaries is not yet stable in the
bootstrap compiler; callers scale max_width accordingly.

## Scenarios

### line_break

#### find_break_opportunities: 'hello world' has break at position 5 (space), kind Soft

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bps = find_break_opportunities("hello world")
expect(bps.len()).to_equal(1)
val bp = bps[0]
expect(bp.position).to_equal(5)
val is_soft = bp.kind == BreakKind.Soft
expect(is_soft).to_equal(true)
expect(bp.break_before).to_equal(true)
```

</details>

#### find_break_opportunities: 'a\\nb' has break at position 1, kind Hard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bps = find_break_opportunities("a\nb")
expect(bps.len()).to_equal(1)
val bp = bps[0]
expect(bp.position).to_equal(1)
val is_hard = bp.kind == BreakKind.Hard
expect(is_hard).to_equal(true)
```

</details>

#### find_break_opportunities: empty string returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bps = find_break_opportunities("")
expect(bps.len()).to_equal(0)
```

</details>

#### wrap_text: 'hello world' with width 66 (at 6px/char) fits on one line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 11 chars * 6px = 66px — width budget 66 exactly fits.
val lines = wrap_text("hello world", 66.0, 6.0)
expect(lines.len()).to_equal(1)
val ln = lines[0]
expect(ln.start).to_equal(0)
expect(ln.end).to_equal(11)
expect(ln.width).to_be_less_than(66.001)
```

</details>

#### wrap_text: 'hello world' with width 36 breaks into two lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'hello' = 30px fits under 36; adding ' world' overflows.
val lines = wrap_text("hello world", 36.0, 6.0)
expect(lines.len()).to_equal(2)
val first = lines[0]
expect(first.start).to_equal(0)
expect(first.end).to_equal(5)
val second = lines[1]
expect(second.start).to_equal(6)
expect(second.end).to_equal(11)
```

</details>

#### wrap_text: 'a\\nb\\nc' with large width produces 3 lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = wrap_text("a\nb\nc", 600.0, 6.0)
expect(lines.len()).to_equal(3)
expect(lines[0].start).to_equal(0)
expect(lines[0].end).to_equal(1)
expect(lines[1].start).to_equal(2)
expect(lines[1].end).to_equal(3)
expect(lines[2].start).to_equal(4)
expect(lines[2].end).to_equal(5)
```

</details>

#### wrap_text: 'verylongwordhere' with width 30 breaks mid-word

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 16 chars, width 30 = only 5 chars per line — must split mid-word.
val lines = wrap_text("verylongwordhere", 30.0, 6.0)
expect(lines.len()).to_be_greater_than(1)
val first = lines[0]
expect(first.start).to_equal(0)
val first_len = first.end - first.start
expect(first_len).to_be_less_than(6)
expect(first_len).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
