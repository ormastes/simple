# T32 Version Detect Specification

> <details>

<!-- sdn-diagram:id=t32_version_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_version_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_version_detect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_version_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Version Detect Specification

## Scenarios

### list_has utility

#### finds present item

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["core", "execute", "object"]
expect(list_has(items, "core")).to_equal(true)
expect(list_has(items, "execute")).to_equal(true)
```

</details>

#### returns false for missing item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["core", "execute"]
expect(list_has(items, "fdx")).to_equal(false)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [text] = []
expect(list_has(items, "anything")).to_equal(false)
```

</details>

### Function name lists

#### core has 16 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_core_function_names()
expect(names.len()).to_equal(16)
```

</details>

#### execute has 7 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_execute_function_names()
expect(names.len()).to_equal(7)
```

</details>

#### memory has 16 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_memory_function_names()
expect(names.len()).to_equal(16)
```

</details>

#### register has 13 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_register_function_names()
expect(names.len()).to_equal(13)
```

</details>

#### breakpoint has 3 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_breakpoint_function_names()
expect(names.len()).to_equal(3)
```

</details>

#### trace has 2 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_trace_function_names()
expect(names.len()).to_equal(2)
```

</details>

#### fdx has 7 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_fdx_function_names()
expect(names.len()).to_equal(7)
```

</details>

#### notify has 4 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_notify_function_names()
expect(names.len()).to_equal(4)
```

</details>

#### direct has 17 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = t32_direct_function_names()
expect(names.len()).to_equal(17)
```

</details>

#### total function count covers all API groups

1. + t32 execute function names
2. + t32 memory function names
3. + t32 register function names
4. + t32 breakpoint function names
5. + t32 trace function names
6. + t32 fdx function names
7. + t32 notify function names
8. + t32 direct function names


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = (t32_core_function_names().len()
    + t32_execute_function_names().len()
    + t32_memory_function_names().len()
    + t32_register_function_names().len()
    + t32_breakpoint_function_names().len()
    + t32_trace_function_names().len()
    + t32_fdx_function_names().len()
    + t32_notify_function_names().len()
    + t32_direct_function_names().len())
# 16+7+16+13+3+2+7+4+17 = 85 bound symbols across modules
# (Object API handles are in the Object module, not counted here)
expect(total).to_be_greater_than(80)
```

</details>

### T32ApiInfo struct

#### creates with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = T32ApiInfo(
    revision: 0,
    has_core: true,
    has_execute_api: false,
    has_object_api: false,
    has_notify_api: false,
    has_fdx_api: false,
    has_direct_api: false,
    supported_groups: ["core"]
)
expect(info.revision).to_equal(0)
expect(info.has_core).to_equal(true)
expect(info.has_execute_api).to_equal(false)
expect(info.supported_groups.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/remote/t32_ffi/t32_version_detect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- list_has utility
- Function name lists
- T32ApiInfo struct

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
