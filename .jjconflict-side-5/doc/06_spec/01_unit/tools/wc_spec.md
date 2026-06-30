# Wc Specification

> <details>

<!-- sdn-diagram:id=wc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wc_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wc Specification

## Scenarios

### wc tool

#### word counting

#### counts words in simple text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_words("hello world foo")
expect(count).to_equal(3)
```

</details>

#### counts words with multiple spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_words("hello   world")
expect(count).to_equal(2)
```

</details>

#### counts words with tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_words("hello\tworld")
expect(count).to_equal(2)
```

</details>

#### counts zero words in empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_words("")
expect(count).to_equal(0)
```

</details>

#### counts single word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_words("hello")
expect(count).to_equal(1)
```

</details>

#### line counting

#### counts newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_lines("line1\nline2\nline3\n")
expect(count).to_equal(3)
```

</details>

#### counts zero lines in empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_lines("")
expect(count).to_equal(0)
```

</details>

#### counts no newline as zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_lines("no newline")
expect(count).to_equal(0)
```

</details>

#### max line length

#### finds longest line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_len = max_line_length("short\na much longer line\nmed")
expect(max_len).to_equal(18)
```

</details>

#### handles single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_len = max_line_length("hello")
expect(max_len).to_equal(5)
```

</details>

#### formatting

#### right-aligns count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatted = format_count(42, 7)
expect(formatted).to_equal("     42")
```

</details>

#### handles count wider than width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatted = format_count(12345, 3)
expect(formatted).to_equal("12345")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/wc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wc tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
