# Wine Process Session Import Transaction Rollback Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_import_transaction_rollback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_import_transaction_rollback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_import_transaction_rollback_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_import_transaction_rollback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Transaction Rollback Specification

## Scenarios

### Wine process session import loader transaction rollback

#### aborts before VMA patching when modeled loader state rolls back

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_loader_transaction_in_vma(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(0)
expect(result.rollback_count).to_equal(2)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("import-loader-rollback-complete")
expect(result.evidence).to_contain("import-loader-vma-transaction-aborted")
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
| Source | `test/01_unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session import loader transaction rollback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
