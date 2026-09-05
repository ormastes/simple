# Query Diagnostics Specification

> <details>

<!-- sdn-diagram:id=query_diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_diagnostics_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Diagnostics Specification

## Scenarios

### query diagnostics helpers

#### splits structured error metadata into core related and help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val structured = _split_structured_error("10:4: variable not found|||RELATED:3:1:declared here|||HELP:did you mean `value`?")
expect(structured.0).to_equal("10:4: variable not found")
expect(structured.1.len()).to_equal(1)
expect(structured.1[0]).to_equal("3:1:declared here")
expect(structured.2).to_equal("did you mean `value`?")
```

</details>

#### extracts explicit error code before fallback inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = _extract_error_code("error[E1234]: example failure", "TypeError")
expect(code).to_equal("E1234")
```

</details>

#### keeps lint json collection in the lint orchestrator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/app/cli/query_lint.spl") ?? ""
expect(content.contains("fn _collect_lint_diagnostics_json(file: text, source: text)")).to_equal(true)
expect(content.contains("_emit_source_lint_diagnostics(file, source, \"json\")")).to_equal(true)
```

</details>

### query dispatcher boundaries

#### dispatcher delegates diagnostics commands through query_rich imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/app/cli/query.spl") ?? ""
expect(content.contains("use app.cli.query_rich.{")).to_equal(true)
expect(content.contains("query_check")).to_equal(true)
expect(content.contains("query_workspace_diagnostics")).to_equal(true)
```

</details>

#### dispatcher no longer defines local fallback diagnostics helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/app/cli/query.spl") ?? ""
expect(not content.contains("fn _query_check_json(")).to_equal(true)
expect(not content.contains("fn _query_diag(")).to_equal(true)
expect(not content.contains("fn _query_line_of(")).to_equal(true)
expect(not content.contains("fn _query_line_after(")).to_equal(true)
expect(not content.contains("fn _query_error_count(")).to_equal(true)
expect(not content.contains("fn query_check(")).to_equal(true)
expect(not content.contains("fn query_workspace_diagnostics(")).to_equal(true)
```

</details>

#### diagnostics module depends on lint orchestrator instead of low-level lint internals

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/app/cli/query_diagnostics.spl") ?? ""
expect(content.contains("use app.cli.query_lint.{")).to_equal(true)
expect(content.contains("use app.cli.query_lint_checks.{")).to_equal(false)
expect(content.contains("use app.cli.query_lint_scan.{")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_diagnostics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query diagnostics helpers
- query dispatcher boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
