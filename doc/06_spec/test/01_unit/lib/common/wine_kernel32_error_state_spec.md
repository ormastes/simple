# Wine Kernel32 Error State Specification

> 1. wine kernel32 error state new

<!-- sdn-diagram:id=wine_kernel32_error_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_error_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_error_state_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_error_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Error State Specification

## Scenarios

### Wine KERNEL32 error-state bridge

#### sets, gets, and formats a bounded last-error code

1. wine kernel32 error state new
   - Expected: result.ok is true
   - Expected: result.code equals `87`
   - Expected: result.state.symbol equals `ERROR_INVALID_PARAMETER`
   - Expected: result.message equals `The parameter is incorrect.`
   - Expected: result.operations equals `SetLastError GetLastError FormatMessageW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    87
)

expect(result.ok).to_equal(true)
expect(result.code).to_equal(87)
expect(result.state.symbol).to_equal("ERROR_INVALID_PARAMETER")
expect(result.message).to_equal("The parameter is incorrect.")
expect(result.operations).to_equal("SetLastError GetLastError FormatMessageW")
```

</details>

#### exposes direct error-state helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = wine_kernel32_set_last_error(wine_kernel32_error_state_new(), 2)
val fetched = wine_kernel32_get_last_error(updated)
val formatted = wine_kernel32_format_message_w(updated, fetched.code)

expect(fetched.ok).to_equal(true)
expect(fetched.code).to_equal(2)
expect(fetched.message).to_equal("ERROR_FILE_NOT_FOUND")
expect(formatted.message).to_equal("The system cannot find the file specified.")
```

</details>

#### keeps error-state dispatch ordered and bounded

1. wine kernel32 error state new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-error-state-sequence-expected:SetLastError`
2. wine kernel32 error state new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_error_state(
    ["GetLastError", "SetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    87
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-error-state-sequence-expected:SetLastError")

val wrong_family = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "HeapAlloc"],
    wine_kernel32_error_state_new(),
    87
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid modeled error codes

1. wine kernel32 error state new
   - Expected: result.ok is false
   - Expected: result.error equals `SetLastError:invalid-error-code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_error_state(
    ["SetLastError", "GetLastError", "FormatMessageW"],
    wine_kernel32_error_state_new(),
    -1
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("SetLastError:invalid-error-code")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_error_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 error-state bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
