# Simpleos Wine Process Import Patch Records Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_import_patch_records_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_import_patch_records_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_import_patch_records_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_import_patch_records_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Patch Records Specification

## Scenarios

### SimpleOS Wine import patch records

### REQ-033: descriptor-qualified thunk patch record planning

#### should plan descriptor-qualified thunk patch records without writing IATs

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_descriptor_thunk_patch_records(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.records.len()).to_equal(4)
expect(result.records[0].dll_name).to_equal("KERNEL32.dll")
expect(result.records[0].symbol).to_equal("GetStdHandle")
expect(result.records[0].proc_address).to_equal(0x120000 + 5)
expect(result.records[3].dll_name).to_equal("USER32.dll")
expect(result.records[3].symbol).to_equal("MessageBoxW")
expect(result.records[3].iat_rva).to_equal(0x21a0)
expect(result.records[3].proc_address).to_equal(0x121000 + 6)
expect(result.evidence).to_contain("import-descriptor-patch-records-planned")
expect(result.evidence).to_contain("import-descriptor-iat-rvas-recorded")
expect(result.evidence).to_contain("no-iat-written")
expect(result.status).to_equal("import-descriptor-patch-records-planned")
```

</details>

#### should reject descriptor patch records when modeled exports are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_descriptor_thunk_patch_records(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.records.len()).to_equal(0)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_patch_records_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine import patch records
- REQ-033: descriptor-qualified thunk patch record planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
