# Query Ast Query Integration Specification

> <details>

<!-- sdn-diagram:id=query_ast_query_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_ast_query_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_ast_query_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_ast_query_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Ast Query Integration Specification

## Scenarios

### AST Query Integration

#### keeps AST query parser and executor available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_ast_query.spl") ?? ""

expect(source).to_contain("struct _AstPattern")
expect(source).to_contain("struct _AstPred")
expect(source).to_contain("fn _parse_ast_pattern(query_str: text) -> _AstPattern")
expect(source).to_contain("fn _match_against_file(pattern: _AstPattern, file: text) -> [_QueryMatch]")
expect(source).to_contain("fn engine_ast_query(query_str: text, files: [text], format_str: text) -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_ast_query_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AST Query Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
