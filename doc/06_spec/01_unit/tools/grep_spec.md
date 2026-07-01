# Grep Specification

> <details>

<!-- sdn-diagram:id=grep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grep_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grep Specification

## Scenarios

### grep tool

#### basic matching

#### matches simple substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello world", "world", false, false, false)
expect(result).to_equal(true)
```

</details>

#### rejects non-matching line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello world", "foo", false, false, false)
expect(result).to_equal(false)
```

</details>

#### case insensitive

#### matches ignoring case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("Hello World", "hello", true, false, false)
expect(result).to_equal(true)
```

</details>

#### matches uppercase pattern against lowercase text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello world", "HELLO", true, false, false)
expect(result).to_equal(true)
```

</details>

#### whole word matching

#### matches whole word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello world", "hello", false, true, false)
expect(result).to_equal(true)
```

</details>

#### rejects partial word match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("helloworld", "hello", false, true, false)
expect(result).to_equal(false)
```

</details>

#### whole line matching

#### matches entire line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello", "hello", false, false, true)
expect(result).to_equal(true)
```

</details>

#### rejects partial line match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = line_matches("hello world", "hello", false, false, true)
expect(result).to_equal(false)
```

</details>

#### word character detection

#### detects letter as word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("a")).to_equal(true)
```

</details>

#### detects digit as word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("5")).to_equal(true)
```

</details>

#### detects underscore as word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("_")).to_equal(true)
```

</details>

#### rejects space as non-word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char(" ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/grep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- grep tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
