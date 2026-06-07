# Wine Process Session Import Entrypoint Handoff Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_import_entrypoint_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_import_entrypoint_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_import_entrypoint_handoff_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_import_entrypoint_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Entrypoint Handoff Specification

## Scenarios

### Wine process session imported entrypoint handoff

#### prepares a patched-image entrypoint handoff after loader state and VMA import patching

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_imported_entrypoint_handoff(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x400000)
expect(result.entry_address).to_equal(0x402000)
expect(result.module_count).to_equal(2)
expect(result.patched_count).to_equal(4)
expect(result.evidence).to_contain("import-loader-vma-transaction-complete")
expect(result.evidence).to_contain("imported-entrypoint-handoff-ready")
expect(result.evidence).to_contain("entrypoint-mapped")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("imported-entrypoint-handoff-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_import_entrypoint_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session imported entrypoint handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
