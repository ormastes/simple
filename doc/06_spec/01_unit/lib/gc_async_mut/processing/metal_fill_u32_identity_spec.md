# Metal ProcessingIR Device Identity Specification

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

## Scenarios

### Metal ProcessingIR device identity

#### derives a stable identity from device metadata rather than a buffer handle

The identity is deterministic for the same Metal device name and memory
metadata, changes for a different device, and fails closed when either required
field is missing.

<details>
<summary>Executable SSpec</summary>

```simple
val first = processing_metal_device_identity("Test Metal GPU", 8589934592)
val repeated = processing_metal_device_identity("Test Metal GPU", 8589934592)
val other_device = processing_metal_device_identity("Other Metal GPU", 8589934592)

expect(first).to_be_greater_than(0)
expect(repeated).to_equal(first)
assert_not_equal(other_device, first)
expect(processing_metal_device_identity("", 8589934592)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", 0)).to_equal(0)
```

</details>

Execution status: not run; TODO 548 blocks the deployed pure-Simple compiler.
