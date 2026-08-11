# Query Visibility Workspace Symbols Specification

> 1. check

<!-- sdn-diagram:id=query_visibility_workspace_symbols_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_visibility_workspace_symbols_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_visibility_workspace_symbols_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_visibility_workspace_symbols_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Workspace Symbols Specification

## Scenarios

### query_visibility workspace-symbols CLI

#### returns reachable symbols with structured visibility metadata

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
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query lsp_main --requester src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"lsp_main\""))
check(stdout.contains("\"simpleVisibility\""))
check(stdout.contains("\"display\":\"private\""))
check(stderr == "")
```

</details>

#### filters non reachable boundary-private symbols across boundaries

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query query_visibility --requester src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
expect(stdout.trim()).to_equal("[]")
check(stderr == "")
```

</details>

#### returns same-boundary private symbols in stable ranked order

1. check
2. check
3. check
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query query_visibility --requester src/app/cli/query_visibility.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"query_visibility_main\""))
check(stdout.contains("\"name\":\"query_visibility_workspace_symbols\""))
val main_idx = stdout.index_of("\"name\":\"query_visibility_main\"") ?? -1
val workspace_idx = stdout.index_of("\"name\":\"query_visibility_workspace_symbols\"") ?? -1
check(main_idx >= 0)
check(workspace_idx >= 0)
check(main_idx < workspace_idx)
check(stdout.contains("\"boundaryModule\":\"app.cli\""))
check(stderr == "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/query_visibility_workspace_symbols_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query_visibility workspace-symbols CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
