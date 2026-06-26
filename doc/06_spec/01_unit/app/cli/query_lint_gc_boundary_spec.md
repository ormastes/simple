# Query Lint Gc Boundary Specification

> <details>

<!-- sdn-diagram:id=query_lint_gc_boundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_lint_gc_boundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_lint_gc_boundary_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_lint_gc_boundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Lint Gc Boundary Specification

## Scenarios

### query lint GC family boundary diagnostics

#### warns when no-gc runtime source imports gc async family

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = collected_json_for(
    "src/lib/nogc_sync_mut/example.spl",
    "use std.gc_async_mut.task\n")
expect(diagnostics).to_contain("gc_boundary_crossing")
expect(diagnostics).to_contain("imports GC family")
```

</details>

#### warns when noalloc runtime source imports allocating no-gc family

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = collected_json_for(
    "src/lib/nogc_async_mut_noalloc/example.spl",
    "use std.nogc_async_mut.task\n")
expect(diagnostics).to_contain("gc_boundary_crossing")
expect(diagnostics).to_contain("imports allocating family")
```

</details>

#### does not warn when noalloc runtime source imports common family

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _collect_lint_diagnostics_json(
    "src/lib/nogc_async_mut_noalloc/example.spl",
    "use std.common.text\n")
expect(result.1.join("\n")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_lint_gc_boundary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query lint GC family boundary diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
