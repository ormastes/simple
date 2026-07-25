# Lint Text Specification

> <details>

<!-- sdn-diagram:id=lint_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_text_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Text Specification

## Scenarios

### lint_text helpers

#### count_triple_quotes returns 0 for empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_triple_quotes("")).to_equal(0)
```

</details>

#### count_triple_quotes returns 0 for plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_triple_quotes("    val x = 1")).to_equal(0)
```

</details>

#### count_triple_quotes counts one opener

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_triple_quotes("    \"\"\"docstring start")).to_equal(1)
```

</details>

#### count_triple_quotes counts a same-line pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_triple_quotes("    \"\"\"one-liner\"\"\"")).to_equal(2)
```

</details>

#### iter_code_lines yields all lines when no docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f():\n    var x = 1\n    x"
val lines = iter_code_lines(src)
expect(lines.len()).to_equal(3)
expect(lines[0].line_num).to_equal(1)
expect(lines[0].trimmed).to_equal("fn f():")
expect(lines[2].trimmed).to_equal("x")
```

</details>

#### iter_code_lines skips a multi-line docstring body

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f():\n    \"\"\"\n    docs body\n    \"\"\"\n    x"
val lines = iter_code_lines(src)
# Yielded: 'fn f():' (1), '"""' closing (4), 'x' (5).  Skipped: opener (2), body (3).
expect(lines.len()).to_equal(3)
expect(lines[0].line_num).to_equal(1)
expect(lines[1].line_num).to_equal(4)
expect(lines[2].line_num).to_equal(5)
```

</details>

#### iter_code_lines treats single-line docstring as code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f():\n    \"\"\"summary\"\"\"\n    x"
val lines = iter_code_lines(src)
expect(lines.len()).to_equal(3)
expect(lines[1].trimmed).to_equal("\"\"\"summary\"\"\"")
```

</details>

#### iter_code_lines preserves 1-based line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "a\nb\nc"
val lines = iter_code_lines(src)
expect(lines[0].line_num).to_equal(1)
expect(lines[1].line_num).to_equal(2)
expect(lines[2].line_num).to_equal(3)
```

</details>

#### iter_code_lines handles back-to-back docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "x\n\"\"\"\nA\n\"\"\"\ny\n\"\"\"\nB\n\"\"\"\nz"
val lines = iter_code_lines(src)
# Yielded line_nums: 1 (x), 4 (close-1), 5 (y), 8 (close-2), 9 (z).
expect(lines.len()).to_equal(5)
expect(lines[0].line_num).to_equal(1)
expect(lines[1].line_num).to_equal(4)
expect(lines[2].line_num).to_equal(5)
expect(lines[3].line_num).to_equal(8)
expect(lines[4].line_num).to_equal(9)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/lint_text_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lint_text helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
