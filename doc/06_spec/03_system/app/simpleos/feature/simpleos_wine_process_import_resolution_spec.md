# Simpleos Wine Process Import Resolution Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_import_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_import_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_import_resolution_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_import_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Resolution Specification

## Scenarios

### SimpleOS Wine import resolution

### REQ-032: modeled multi-DLL import resolution

#### should plan modeled module and procedure resolution without patching IATs

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_resolution(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.resolved_count).to_equal(4)
expect(result.evidence).to_contain("import-module-handles-modeled")
expect(result.evidence).to_contain("import-proc-addresses-modeled")
expect(result.evidence).to_contain("no-iat-patched")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-resolution-planned")
```

</details>

#### should reject missing modeled exports before IAT patching

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_resolution(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.resolved_count).to_equal(3)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine import resolution
- REQ-032: modeled multi-DLL import resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
