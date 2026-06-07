# Multiline String Specification

> <details>

<!-- sdn-diagram:id=multiline_string_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiline_string_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiline_string_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiline_string_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline String Specification

## Scenarios

### multiline strings

#### triple-quoted string is a string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """hello world"""
expect(s).to_equal("hello world")
```

</details>

#### triple-quoted string with embedded quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """say "hello" to me"""
expect(s).to_equal("say \"hello\" to me")
```

</details>

#### triple-quoted empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """"""
expect(s).to_equal("")
```

</details>

#### triple-quoted with single quotes inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """it's fine"""
expect(s).to_equal("it's fine")
```

</details>

#### triple-quoted concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = """hello """
val b = """world"""
val c = a + b
expect(c).to_equal("hello world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/multiline_string_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- multiline strings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
