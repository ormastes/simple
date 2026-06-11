# Wine Process Session Loader State Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_loader_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_loader_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_loader_state_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_loader_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Loader State Specification

## Scenarios

### Wine process session import loader state

#### tracks modeled module refcounts and releases successful import loads

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(2)
expect(result.rollback_count).to_equal(0)
expect(result.max_ref_count).to_equal(2)
expect(result.evidence).to_contain("import-loader-state-planned")
expect(result.evidence).to_contain("import-loader-refcounts-tracked")
expect(result.evidence).to_contain("import-loader-modules-loaded")
expect(result.evidence).to_contain("import-loader-modules-released")
expect(result.evidence).to_contain("import-loader-refcounts-restored")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-loader-state-planned")
```

</details>

#### rolls back modeled module loads when import resolution fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(0)
expect(result.rollback_count).to_equal(2)
expect(result.max_ref_count).to_equal(2)
expect(result.evidence).to_contain("import-loader-rollback-complete")
expect(result.evidence).to_contain("import-loader-refcounts-restored")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_loader_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session import loader state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
