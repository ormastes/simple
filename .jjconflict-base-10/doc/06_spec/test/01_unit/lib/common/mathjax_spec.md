# Mathjax Specification

> <details>

<!-- sdn-diagram:id=mathjax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mathjax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mathjax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mathjax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mathjax Specification

## Scenarios

### Mathjax

#### defines LaTeX renderer tables and special forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val math = rt_file_read_text("src/lib/common/math_repr.spl")

expect(math).to_contain("fn _greek_latex(name: text) -> text:")
expect(math).to_contain("if name == \"alpha\": return \"\\\\alpha\"")
expect(math).to_contain("if name == \"Omega\": return \"\\\\Omega\"")
expect(math).to_contain("fn _known_fn_latex(name: text) -> text:")
expect(math).to_contain("if name == \"sin\": return \"\\\\sin\"")
expect(math).to_contain("return [\"\\\\frac{\" + num + \"}{\" + den + \"}\", np]")
expect(math).to_contain("return [\"\\\\sqrt{\" + _sub_latex(ar[0]) + \"}\", np]")
```

</details>

#### defines raw LaTeX and Markdown math entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val math = rt_file_read_text("src/lib/common/math_repr.spl")

expect(math).to_contain("fn _primary_latex(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _power_latex(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _mul_latex(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _expr_latex(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn render_latex_raw(expr: text) -> text:")
expect(math).to_contain("fn to_md(expr: text) -> text:")
expect(math).to_contain("\"$\" + render_latex_raw(expr) + \"$\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mathjax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mathjax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
