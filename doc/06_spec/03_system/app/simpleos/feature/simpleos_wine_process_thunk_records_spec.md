# Simpleos Wine Process Thunk Records Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_thunk_records_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_thunk_records_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_thunk_records_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_thunk_records_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Thunk Records Specification

## Scenarios

### SimpleOS Wine thunk patch records

### REQ-024: bounded thunk patch record planning

#### should plan concrete records for the known KERNEL32 import thunk slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.records.len()).to_equal(3)
expect(result.records[0].symbol).to_equal("GetStdHandle")
expect(result.records[0].thunk_rva).to_equal(0x2060)
expect(result.records[0].name_rva).to_equal(0x2080)
expect(result.records[1].symbol).to_equal("WriteFile")
expect(result.records[1].thunk_rva).to_equal(0x2068)
expect(result.records[2].symbol).to_equal("ExitProcess")
expect(result.records[2].thunk_rva).to_equal(0x2070)
expect(result.evidence).to_contain("import-thunk-records-data-backed")
expect(result.status).to_equal("thunk-records-planned")
```

</details>

#### should reject thunk record planning before load-and-bind passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_kernel32_thunk_patch_records(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.records.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine thunk patch records
- REQ-024: bounded thunk patch record planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
