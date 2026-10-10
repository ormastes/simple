# Conditional Source Lines Specification

> Tests covering Conditional preprocessing preserves source bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conditional Source Lines Specification

## Scenarios

### Conditional preprocessing preserves source bytes

#### retains one empty line for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_pp_split_lines("")).to_equal([""])
```

</details>

#### retains the empty final line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_pp_split_lines("a\n")).to_equal(["a", ""])
```

</details>

#### retains consecutive empty lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_pp_split_lines("\n\n")).to_equal(["", "", ""])
```

</details>

#### preserves CRLF bytes without inventing a final newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_pp_split_lines("a\r\nb\r")).to_equal(["a\r", "b\r"])
```

</details>

#### preserves Unicode comment and final declaration bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# —\n@cfg(x86_64)\nfn value() -> i64:\n    (42)\n"
expect(_pp_split_lines(source).join("\n")).to_equal(source)
expect(_pp_split_lines(source)[3]).to_equal("    (42)")
```

</details>

#### preserves Unicode literals without a final newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn value() -> text:\n    \"한글é\""
expect(_pp_split_lines(source).join("\n")).to_equal(source)
```

</details>

#### preserves embedded NUL

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_pp_split_lines("A\0B\nC")).to_equal(["A\0B", "C"])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/parser/conditional_source_lines_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Conditional preprocessing preserves source bytes.
- Conditional preprocessing preserves source bytes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
