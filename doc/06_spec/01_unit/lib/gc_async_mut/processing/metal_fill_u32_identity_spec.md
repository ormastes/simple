# Metal ProcessingIR Device Identity Specification

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 2 | 2 | 0 | 0 |

## Scenarios

### Metal ProcessingIR device identity

#### derives a stable identity from device metadata rather than a buffer handle

The identity is deterministic for the same Metal device name and memory
metadata, changes for a different device, and fails closed when either required
field is missing. Different memory metadata must also change the identity;
negative memory is rejected while maximum positive `i64` memory remains
representable.

<details>
<summary>Executable SSpec</summary>

```simple
val first = processing_metal_device_identity("Test Metal GPU", 8589934592)
val repeated = processing_metal_device_identity("Test Metal GPU", 8589934592)
val other_device = processing_metal_device_identity("Other Metal GPU", 8589934592)
val other_memory = processing_metal_device_identity("Test Metal GPU", 4294967296)

expect(first).to_be_greater_than(0)
expect(repeated).to_equal(first)
assert_not_equal(other_device, first)
assert_not_equal(other_memory, first)
expect(processing_metal_device_identity("", 8589934592)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", 0)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", -1)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", 9223372036854775807)).to_be_greater_than(0)
```

</details>

#### rejects invalid IR before any Metal device operation

Zero-sized, overflowing, and unsupported requests return their exact validation
reason, empty output, and zero backend provenance without requiring a Metal
host.

<details>
<summary>Executable SSpec</summary>

```simple
_expect_rejected(processing_ir_execute_metal(processing_ir_fill_u32(0, 7u32)), "invalid-element-count")
_expect_rejected(processing_ir_execute_metal(processing_ir_fill_u32(536870912, 7u32)), "output-size-overflow")
_expect_rejected(processing_ir_execute_metal(ProcessingIr(op: 99, element_count: 1, value: 7u32)), "unsupported-op")
```

</details>

Execution status: Linux Rust-seed interpreter pass, 2/2. This proves only
host-independent validation and identity behavior; TODO 548 still blocks
deployed pure-Simple admission, and live Metal execution remains a macOS row.
