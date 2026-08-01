# Simpleos Wine Process Import Transaction Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_import_transaction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_import_transaction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_import_transaction_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_import_transaction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Transaction Specification

## Scenarios

### SimpleOS Wine import loader VMA transaction

### REQ-039: loader-state-gated import VMA patch transaction

#### should patch multi-DLL imports only after modeled loader state has been released

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_loader_transaction_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.released_count).to_equal(2)
expect(result.patched_count).to_equal(4)
expect(result.evidence).to_contain("import-loader-state-before-vma-patch")
expect(result.evidence).to_contain("import-loader-vma-transaction-complete")
expect(result.evidence).to_contain("multi-dll-import-thunks-applied")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-loader-vma-transaction-complete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine import loader VMA transaction
- REQ-039: loader-state-gated import VMA patch transaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
