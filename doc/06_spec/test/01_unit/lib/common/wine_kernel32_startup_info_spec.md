# Wine Kernel32 Startup Info Specification

> 1. wine kernel32 startup info default

<!-- sdn-diagram:id=wine_kernel32_startup_info_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_startup_info_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_startup_info_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_startup_info_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Startup Info Specification

## Scenarios

### Wine KERNEL32 startup info bridge

#### executes bounded startup info and standard handle discovery

1. wine kernel32 startup info default
   - Expected: result.ok is true
   - Expected: result.show_window equals `1`
   - Expected: result.std_input equals `-10`
   - Expected: result.std_output equals `-11`
   - Expected: result.std_error equals `-12`
   - Expected: result.desktop equals `winsta0\\default`
   - Expected: result.operations equals `GetStartupInfoW GetStdHandle GetStdHandle GetStdHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "GetStdHandle"],
    wine_kernel32_startup_info_default()
)

expect(result.ok).to_equal(true)
expect(result.show_window).to_equal(1)
expect(result.std_input).to_equal(-10)
expect(result.std_output).to_equal(-11)
expect(result.std_error).to_equal(-12)
expect(result.desktop).to_equal("winsta0\\default")
expect(result.operations).to_equal("GetStartupInfoW GetStdHandle GetStdHandle GetStdHandle")
```

</details>

#### keeps startup info dispatch ordered and bounded

1. wine kernel32 startup info default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-startup-info-sequence-expected:GetStartupInfoW`
2. wine kernel32 startup info default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_startup_info(
    ["GetStdHandle", "GetStartupInfoW", "GetStdHandle", "GetStdHandle"],
    wine_kernel32_startup_info_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-startup-info-sequence-expected:GetStartupInfoW")

val wrong_family = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "HeapAlloc"],
    wine_kernel32_startup_info_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid standard handle models

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = WineKernel32StartupInfo(show_window: 1, std_input: -10, std_output: 99, std_error: -12, desktop: "winsta0\\default", title: "SimpleOS Wine")
val result = wine_kernel32_execute_startup_info(
    ["GetStartupInfoW", "GetStdHandle", "GetStdHandle", "GetStdHandle"],
    info
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("GetStdHandle:invalid-stdout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_startup_info_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 startup info bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
