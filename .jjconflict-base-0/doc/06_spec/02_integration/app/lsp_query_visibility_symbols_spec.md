# Lsp Query Visibility Symbols Specification

> 1. check

<!-- sdn-diagram:id=lsp_query_visibility_symbols_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_query_visibility_symbols_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_query_visibility_symbols_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_query_visibility_symbols_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Query Visibility Symbols Specification

## Scenarios

### lsp_query symbols visibility surface

#### returns visibility-aware JSON symbols from the lightweight runner

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple src/lib/nogc_sync_mut/lsp/lsp_query.spl symbols src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"lsp_main\""))
check(stdout.contains("\"simpleVisibility\""))
check(stdout.contains("\"boundaryKind\":\"boundary\""))
check(not stderr.contains("error:"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/lsp_query_visibility_symbols_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lsp_query symbols visibility surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
