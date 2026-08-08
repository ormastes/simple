# Query Visibility Surfaces Specification

> 1. check

<!-- sdn-diagram:id=query_visibility_surfaces_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_visibility_surfaces_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_visibility_surfaces_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_visibility_surfaces_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Surfaces Specification

## Scenarios

### query_visibility CLI surfaces

#### reports scoped peer and up visibility in structured JSON

1. check
2. check
3. check
4. check
5. check
6. check
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl symbols src/compiler/10.frontend/testdata/visibility_query_fixture.spl --requester src/compiler/35.semantics/testdata/visibility_query_fixture.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"peer_api\""))
check(stdout.contains("\"display\":\"peer\""))
check(stdout.contains("\"declared\":\"peer\""))
check(stdout.contains("\"reachable\":true"))
check(stdout.contains("\"name\":\"parent_api\""))
check(stdout.contains("\"display\":\"up\""))
check(stdout.contains("\"declared\":\"up\""))
check(stdout.contains("\"reachable\":false"))
check(stderr == "")
```

</details>

#### hover returns markdown contents plus simpleVisibility

1. check
2. check
3. check
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl hover src/lib/nogc_sync_mut/lsp/main.spl 33 10"
)

expect(code).to_equal(0)
check(stdout.contains("\"contents\""))
check(stdout.contains("\"kind\":\"markdown\""))
check(stdout.contains("fn lsp_main():"))
check(stdout.contains("\"simpleVisibility\""))
check(stdout.contains("\"display\":\"private\""))
check(stdout.contains("\"boundaryModule\":\"lib.nogc_sync_mut.lsp\""))
check(stderr == "")
```

</details>

#### completions return structured visibility in item data

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl completions src/lib/nogc_sync_mut/lsp/main.spl 33 10"
)

expect(code).to_equal(0)
check(stdout.contains("\"label\":\"lsp_main\""))
check(stdout.contains("\"detail\":\"[private] fn\""))
check(stdout.contains("\"data\":{\"simpleVisibility\""))
check(stdout.contains("\"display\":\"private\""))
check(stderr == "")
```

</details>

#### document symbols include simpleVisibility on returned symbols

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl symbols src/lib/nogc_sync_mut/lsp/main.spl --requester src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"lsp_main\""))
check(stdout.contains("\"selectionRange\""))
check(stdout.contains("\"simpleVisibility\""))
check(stdout.contains("\"boundaryKind\":\"boundary\""))
check(stderr == "")
```

</details>

#### semantic-tokens returns full-style JSON data

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl semantic-tokens src/app/cli/query_visibility.spl"
)

expect(code).to_equal(0)
check(stdout.starts_with("{\"data\":["))
check(stdout.contains(","))
check(stderr == "")
```

</details>

#### semantic-tokens supports a scoped line range

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (full_stdout, full_stderr, full_code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl semantic-tokens src/app/cli/query_visibility.spl"
)
val (range_stdout, range_stderr, range_code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl semantic-tokens src/app/cli/query_visibility.spl --start-line 1 --end-line 40"
)

expect(full_code).to_equal(0)
expect(range_code).to_equal(0)
check(full_stdout.contains("\"data\":["))
check(range_stdout.contains("\"data\":["))
check(range_stdout.len() < full_stdout.len())
check(full_stderr == "")
check(range_stderr == "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/query_visibility_surfaces_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query_visibility CLI surfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
