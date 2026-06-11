# Wine Ntdll System Info Specification

> <details>

<!-- sdn-diagram:id=wine_ntdll_system_info_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_system_info_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_system_info_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_system_info_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll System Info Specification

## Scenarios

### Wine NTDLL system information bridge

#### executes a bounded NtQuerySystemInformation sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], _classes(), wine_ntdll_system_info_default())

expect(result.ok).to_equal(true)
expect(result.page_size).to_equal(4096)
expect(result.allocation_granularity).to_equal(65536)
expect(result.processor_count).to_equal(4)
expect(result.timer_resolution_100ns).to_equal(156250)
expect(result.system_root).to_equal("C:\\windows")
expect(result.classes).to_equal("SystemBasicInformation SystemProcessorInformation SystemTimeOfDayInformation")
expect(result.operations).to_equal("NtQuerySystemInformation")
```

</details>

#### keeps system information dispatch and classes bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrong_family = wine_ntdll_execute_system_info(["NtCreateFile"], _classes(), wine_ntdll_system_info_default())
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")

val wrong_class = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], ["SystemProcessorInformation", "SystemBasicInformation", "SystemTimeOfDayInformation"], wine_ntdll_system_info_default())
expect(wrong_class.ok).to_equal(false)
expect(wrong_class.error).to_equal("ntdll-system-info-class-expected:SystemBasicInformation")
```

</details>

#### rejects invalid system information facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = WineNtdllSystemInfo(
    page_size: 4096,
    allocation_granularity: 65536,
    processor_count: 0,
    timer_resolution_100ns: 156250,
    system_root: "C:\\windows"
)
val result = wine_ntdll_execute_system_info(["NtQuerySystemInformation"], _classes(), invalid)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtQuerySystemInformation:invalid-processor-count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_system_info_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL system information bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
