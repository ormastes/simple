# Simpleos Wine Dll Search Order Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_search_order_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_search_order_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_search_order_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_search_order_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll Search Order Specification

## Scenarios

### SimpleOS Wine DLL search order

### REQ-041: modeled DLL search order without host DLL execution

#### should plan KnownDlls-first DLL candidates without loading host files

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_plan_dll_search_order(
    "kernel32.dll",
    "C:\\Games",
    "C:\\Users\\Player",
    ["D:\\GameBin"],
    ["kernel32.dll", "ntdll.dll"]
)

expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.search_roots[0]).to_equal("\\KnownDlls")
expect(result.search_roots[1]).to_equal("C:\\Games")
expect(result.search_roots[6]).to_equal("D:\\GameBin")
expect(result.candidate_paths[0]).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("knowndlls-first")
expect(result.evidence).to_contain("application-directory")
expect(result.evidence).to_contain("no-host-filesystem-access")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.status).to_equal("dll-search-order-modeled")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_search_order_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine DLL search order
- REQ-041: modeled DLL search order without host DLL execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
