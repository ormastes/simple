# Unicode Math Specification

> <details>

<!-- sdn-diagram:id=unicode_math_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unicode_math_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unicode_math_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unicode_math_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unicode Math Specification

## Scenarios

### UnicodeMath

#### defines Unicode Greek and superscript rendering tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val math = rt_file_read_text("src/lib/common/math_repr.spl")

expect(math).to_contain("fn _greek_unicode(name: text) -> text:")
expect(math).to_contain("if name == \"alpha\": return \"α\"")
expect(math).to_contain("if name == \"Gamma\": return \"Γ\"")
expect(math).to_contain("if name == \"Omega\": return \"Ω\"")
expect(math).to_contain("if name == \"nabla\": return \"∇\"")
expect(math).to_contain("fn _superscript_digit(ch: text) -> text:")
expect(math).to_contain("if ch == \"2\": return \"²\"")
expect(math).to_contain("fn _to_superscript(s: text) -> text:")
```

</details>

#### defines pretty renderer parser stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val math = rt_file_read_text("src/lib/common/math_repr.spl")

expect(math).to_contain("fn _primary_pretty(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _power_pretty(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _mul_pretty(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn _expr_pretty(tokens: [text], pos: i64) -> [text]:")
expect(math).to_contain("fn to_pretty(expr: text) -> text:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/unicode_math_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UnicodeMath

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
