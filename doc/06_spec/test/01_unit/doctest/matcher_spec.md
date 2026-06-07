# Matcher Specification

> <details>

<!-- sdn-diagram:id=matcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=matcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

matcher_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=matcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matcher Specification

## Scenarios

### DoctestMatcher

#### match_output

#### matches exact output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "42"
val expected = Expected.Output("42")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches with trailing whitespace normalization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "42  \n"
val expected = Expected.Output("42")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails on mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "42"
val expected = Expected.Output("43")
val result = match_output(actual, expected)
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("mismatch")
```

</details>

#### matches multi-line output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "line1\nline2\nline3"
val expected = Expected.Output("line1\nline2\nline3")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = ""
val expected = Expected.Empty
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails when expecting empty but got output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "unexpected"
val expected = Expected.Empty
val result = match_output(actual, expected)
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("Expected no output")
```

</details>

#### match_exception

#### matches exception type

1. Expected Exception
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_exception("ValueError", "some message",
                        Expected.Exception("ValueError", nil))
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches exception type and message

1. Expected Exception
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_exception("ValueError", "invalid input",
                        Expected.Exception("ValueError", "invalid"))
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails on wrong exception type

1. Expected Exception
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_exception("TypeError", "msg",
                        Expected.Exception("ValueError", nil))
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("Expected ValueError")
```

</details>

#### fails on wrong message

1. Expected Exception
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_exception("ValueError", "wrong message",
                        Expected.Exception("ValueError", "expected message"))
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("message mismatch")
```

</details>

#### fails when expected output but got exception

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_exception("ValueError", "msg", Expected.Output("42"))
expect(result.is_fail()).to_equal(true)
```

</details>

#### wildcard_match

#### matches with dot wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wildcard_match("abc", "a.c")).to_equal(true)
expect(wildcard_match("a1c", "a.c")).to_equal(true)
expect(wildcard_match("axc", "a.c")).to_equal(true)
```

</details>

#### matches with star wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wildcard_match("hello world", "hello*")).to_equal(true)
expect(wildcard_match("hello world", "*world")).to_equal(true)
expect(wildcard_match("hello world", "hello*world")).to_equal(true)
```

</details>

#### matches UUID pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uuid = "550e8400-e29b-41d4-a716-446655440000"
val pattern = "........-....-....-....-............"
expect(wildcard_match(uuid, pattern)).to_equal(true)
```

</details>

#### matches timestamp pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timestamp = "1702345678"
val pattern = "1702*"
expect(wildcard_match(timestamp, pattern)).to_equal(true)
```

</details>

#### fails on non-matching pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wildcard_match("abc", "a.d")).to_equal(false)
expect(wildcard_match("hello", "world")).to_equal(false)
```

</details>

#### handles multiple wildcards

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wildcard_match("ab12cd34ef", "ab..cd..ef")).to_equal(true)
expect(wildcard_match("prefix123suffix456", "prefix*suffix*")).to_equal(true)
```

</details>

#### exact_match

#### matches identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exact_match("hello", "hello")).to_equal(true)
```

</details>

#### normalizes whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exact_match("hello  ", "hello")).to_equal(true)
expect(exact_match("hello\n", "hello")).to_equal(true)
expect(exact_match(" hello ", " hello")).to_equal(true)
```

</details>

#### fails on different strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exact_match("hello", "world")).to_equal(false)
```

</details>

#### normalize

#### strips trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize("hello  ")).to_equal("hello")
expect(normalize("hello\t\n")).to_equal("hello")
```

</details>

#### strips trailing whitespace from each line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize("line1  \nline2  ")).to_equal("line1\nline2")
```

</details>

#### trims leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize("  hello")).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/doctest/matcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DoctestMatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
