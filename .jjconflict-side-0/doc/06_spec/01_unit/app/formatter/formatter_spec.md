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

#### keeps query document-formatting command wired to formatter factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_formatting.spl") ?? ""

expect(source).to_contain("use compiler.tools.formatter.main.{make_formatter}")
expect(source).to_contain("fn query_document_formatting(file: text) -> i64")
expect(source).to_contain("val fmt = make_formatter()")
expect(source).to_contain("fmt.format_file(clean_file)")
```

</details>

#### keeps packaged formatter artifact present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = rt_file_read_text("src/app/formatter/main.smf") ?? ""
expect(artifact.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter/formatter_spec.spl` |
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
