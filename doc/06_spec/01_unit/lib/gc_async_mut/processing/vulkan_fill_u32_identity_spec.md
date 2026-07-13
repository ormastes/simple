# Vulkan ProcessingIR Device Identity Specification

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

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
```

</details>

Execution status: not run; TODO 548 blocks the deployed pure-Simple compiler.
