# CUDA ProcessingIR Pre-Device Validation Specification

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

## Scenarios

### CUDA ProcessingIR pre-device validation

#### rejects invalid IR with zero device provenance

Zero-sized, overflowing, and unsupported requests fail before any CUDA driver
operation. Every failure has its exact validation reason, empty output, and
zero backend handle/device identity.

<details>
<summary>Executable SSpec</summary>

```simple
val zero = processing_ir_execute_cuda(processing_ir_fill_u32(0, 7u32))
expect(zero.reason).to_equal("invalid-element-count")
_expect_rejected(zero, "invalid-element-count")
_expect_rejected(processing_ir_execute_cuda(processing_ir_fill_u32(536870912, 7u32)), "output-size-overflow")
_expect_rejected(processing_ir_execute_cuda(ProcessingIr(op: 99, element_count: 1, value: 7u32)), "unsupported-op")
```

</details>

Execution status: Linux Rust-seed interpreter pass, 1/1. This proves only
host-independent pre-device validation; live CUDA execution evidence remains
separate.
