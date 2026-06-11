# Interp Split Ws Specification

> <details>

<!-- sdn-diagram:id=interp_split_ws_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interp_split_ws_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interp_split_ws_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interp_split_ws_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Split Ws Specification

## Scenarios

### split(newline) whitespace stripping bug

#### demonstrates the bug with split

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_with_indent = "line1\n  indented\n    deeply"
val lines = text_with_indent.split("\n")
# BUG: split("\n") strips leading whitespace
# lines[1] becomes "indented" instead of "  indented"
# We can only verify the content is present, not the indent
expect(_len(lines)).to_equal(3)
expect(_get(lines, 0)).to_equal("line1")
# lines[1] should be "  indented" but bug strips it
val line1 = _get(lines, 1)
expect(line1).to_contain("indented")
```

</details>

#### workaround preserves indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_with_indent = "line1\n  indented\n    deeply"
val lines = _parse_lines_preserving_indent(text_with_indent)
expect(_len(lines)).to_equal(3)
expect(_get(lines, 0)).to_equal("line1")
expect(_get(lines, 1)).to_equal("  indented")
expect(_get(lines, 2)).to_equal("    deeply")
```

</details>

#### workaround handles trailing newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "a\nb\n"
val lines = _parse_lines_preserving_indent(content)
expect(_len(lines)).to_equal(2)
expect(_get(lines, 0)).to_equal("a")
expect(_get(lines, 1)).to_equal("b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_split_ws_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- split(newline) whitespace stripping bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
