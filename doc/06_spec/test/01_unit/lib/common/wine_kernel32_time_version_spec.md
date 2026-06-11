# Wine Kernel32 Time Version Specification

> 1. wine kernel32 time version clock default

<!-- sdn-diagram:id=wine_kernel32_time_version_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_time_version_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_time_version_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_time_version_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Time Version Specification

## Scenarios

### Wine KERNEL32 time and version bridge

#### executes a bounded time and version sequence

1. wine kernel32 time version clock default
   - Expected: result.ok is true
   - Expected: result.tick_count_ms equals `1234`
   - Expected: result.performance_counter equals `987654321`
   - Expected: result.performance_frequency equals `10000000`
   - Expected: result.version_text equals `6.1.7601`
   - Expected: result.platform_id equals `VER_PLATFORM_WIN32_NT`
   - Expected: result.operations equals `GetTickCount QueryPerformanceCounter QueryPerformanceFrequency GetVersion Get... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    wine_kernel32_time_version_clock_default()
)

expect(result.ok).to_equal(true)
expect(result.tick_count_ms).to_equal(1234)
expect(result.performance_counter).to_equal(987654321)
expect(result.performance_frequency).to_equal(10000000)
expect(result.version_text).to_equal("6.1.7601")
expect(result.platform_id).to_equal("VER_PLATFORM_WIN32_NT")
expect(result.operations).to_equal("GetTickCount QueryPerformanceCounter QueryPerformanceFrequency GetVersion GetVersionExW")
```

</details>

#### keeps time/version dispatch ordered and bounded

1. wine kernel32 time version clock default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-time-version-sequence-expected:GetTickCount`
2. wine kernel32 time version clock default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_time_version(
    ["QueryPerformanceCounter", "GetTickCount", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    wine_kernel32_time_version_clock_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-time-version-sequence-expected:GetTickCount")

val wrong_family = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "HeapAlloc"],
    wine_kernel32_time_version_clock_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid clock inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clock = WineKernel32TimeVersionClock(
    tick_count_ms: 1,
    performance_counter: 2,
    performance_frequency: 0,
    version_major: 6,
    version_minor: 1,
    version_build: 7601,
    platform_id: "VER_PLATFORM_WIN32_NT"
)
val result = wine_kernel32_execute_time_version(
    ["GetTickCount", "QueryPerformanceCounter", "QueryPerformanceFrequency", "GetVersion", "GetVersionExW"],
    clock
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("QueryPerformanceFrequency:invalid-frequency")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_time_version_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 time and version bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
