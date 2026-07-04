# Simpleos Wine Process Loader State Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_loader_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_loader_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_loader_state_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_loader_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Loader State Specification

## Scenarios

### SimpleOS Wine process import loader state

### REQ-038: modeled import loader state with refcount release and rollback

#### should own modeled multi-DLL loader state without real DLL loading or PE execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(2)
expect(result.max_ref_count).to_equal(2)
expect(result.evidence).to_contain("import-loader-state-planned")
expect(result.evidence).to_contain("import-loader-refcounts-tracked")
expect(result.evidence).to_contain("import-loader-refcounts-restored")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-loader-state-planned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine process import loader state
- REQ-038: modeled import loader state with refcount release and rollback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
