# Vulkan Icd Sffi Specification

> <details>

<!-- sdn-diagram:id=vulkan_icd_sffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_icd_sffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_icd_sffi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_icd_sffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Icd Sffi Specification

## Scenarios

### Vulkan ICD SFFI shim

#### create_instance returns is_ok=true with positive handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vk_icd_create_instance()
expect(result.is_ok).to_equal(true)
expect(result.instance_handle).to_be_greater_than(0)
expect(result.device_handle).to_be_greater_than(0)
expect(result.dispatch_handle).to_be_greater_than(0)
```

</details>

#### create_device on valid instance returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = vk_icd_create_instance()
val dev = vk_icd_create_device(inst.instance_handle)
expect(dev.is_ok).to_equal(true)
expect(dev.device_handle).to_be_greater_than(0)
```

</details>

#### create_device on invalid instance returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vk_icd_create_device(0)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("invalid-instance")
```

</details>

#### destroy_instance does not panic on valid result

1. vk icd destroy instance
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vk_icd_create_instance()
vk_icd_destroy_instance(result)
expect(1).to_equal(1)
```

</details>

#### two create_instance calls return distinct instance handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = vk_icd_create_instance()
val r2 = vk_icd_create_instance()
expect(r1.instance_handle).to_not_equal(r2.instance_handle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan ICD SFFI shim

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
