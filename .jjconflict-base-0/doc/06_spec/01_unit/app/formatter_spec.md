# Formatter Specification

> <details>

<!-- sdn-diagram:id=formatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Specification

## Scenarios

### Formatter

#### keeps formatter configuration and entry points available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = formatter_source()

expect(source).to_contain("class FormatConfig:")
expect(source).to_contain("class Formatter:")
expect(source).to_contain("static fn with_defaults() -> Formatter")
expect(source).to_contain("fn format_file(self, path: String) -> Result<String, String>")
expect(source).to_contain("fn format_source(self, source: String) -> Result<String, String>")
expect(source).to_contain("fn make_formatter() -> Formatter")
```

</details>

#### keeps formatter line and spacing helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = formatter_source()

expect(source).to_contain("fn count_leading_spaces(line: String) -> Int")
expect(source).to_contain("fn is_definition(line: String) -> Bool")
expect(source).to_contain("fn format_line(line: String, indent: Int) -> [String]")
expect(source).to_contain("fn add_expression_spacing(line: String) -> String")
expect(source).to_contain("fn is_indent_line(line: String) -> Bool")
expect(source).to_contain("fn is_dedent_line(line: String) -> Bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
