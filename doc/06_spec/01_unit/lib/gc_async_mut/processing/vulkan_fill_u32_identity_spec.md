# Vulkan ProcessingIR Device Identity Specification

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 2 | 2 | 0 | 0 |

## Scenarios

### Vulkan ProcessingIR device identity

#### derives a stable identity from the device and driver rather than a buffer handle

The identity is deterministic for the same runtime-selected device/driver
identity, changes with the driver identity, and fails closed when it is missing.

<details>
<summary>Executable SSpec</summary>

```simple
val first = processing_vulkan_device_identity("Test GPU|vendor=1|device=2|driver=1|api=3")
val repeated = processing_vulkan_device_identity("Test GPU|vendor=1|device=2|driver=1|api=3")
val other_driver = processing_vulkan_device_identity("Test GPU|vendor=1|device=2|driver=2|api=3")

expect(first).to_be_greater_than(0)
expect(repeated).to_equal(first)
assert_not_equal(other_driver, first)
expect(processing_vulkan_device_identity("")).to_equal(0)
expect(first).to_be_less_than(2147483648)
```

</details>

#### rejects invalid IR before Vulkan initialization

Zero-sized, overflowing, and unsupported requests return exact validation
reasons, empty output, and zero backend provenance without requiring a Vulkan
host.

<details>
<summary>Executable SSpec</summary>

```simple
val zero = processing_ir_execute_vulkan(processing_ir_fill_u32(0, 7u32))
expect(zero.reason).to_equal("invalid-element-count")
_expect_rejected(zero, "invalid-element-count")
_expect_rejected(processing_ir_execute_vulkan(processing_ir_fill_u32(536870912, 7u32)), "output-size-overflow")
_expect_rejected(processing_ir_execute_vulkan(ProcessingIr(op: 99, element_count: 1, value: 7u32)), "unsupported-op")
```

</details>

Execution status: Linux Rust-seed interpreter pass, 2/2. This proves only
host-independent validation and identity behavior; live Vulkan execution
evidence remains separate.
