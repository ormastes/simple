# X25519mlkem768 Vulkan Snapshot Contract Specification

> Tests covering X25519MLKEM768 Vulkan SPIR-V snapshot contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Vulkan Snapshot Contract Specification

## Scenarios

### X25519MLKEM768 Vulkan SPIR-V snapshot contract

#### should admit exact pinned bytes once and reuse them for session init

- Inspect snapshot admission and the filesystem-free execution path
- "file read bytes
   - Expected: execute_source does not contain `file_read_bytes(`
   - Expected: execute_source does not contain `file_size(`
   - Expected: execute_source does not contain `sha256_u8_hex(`
- "x25519 mlkem768 artifact read exact
- "forward read len
- " vulkan spirv magic valid
- "val warmup reason = self  ensure ready
   - Expected: provider.count("self.session.execute(") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect snapshot admission and the filesystem-free execution path")
val provider = file_read_text(
    "src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl")
val constructor = provider.index_of("static fn create_binaries(")
val execute = provider.index_of("me _execute(")
val shutdown = provider.index_of("me shutdown():", execute)
val constructor_read = provider.index_of(
    "file_read_bytes(forward_artifact_path)", constructor)
val execute_source = provider.slice(execute, shutdown)
expect(constructor_read).to_be_greater_than(constructor)
expect(constructor_read).to_be_less_than(execute)
expect(execute_source.contains("file_read_bytes(")).to_equal(false)
expect(execute_source.contains("file_size(")).to_equal(false)
expect(execute_source.contains("sha256_u8_hex(")).to_equal(false)
expect(provider).to_contain(
    "x25519_mlkem768_artifact_read_exact(")
expect(provider).to_contain(
    "snapshot_read_admitted, forward_size,")
expect(provider).to_contain(
    "forward_read.len().to_i64())")
expect(provider).to_contain(
    "current_forward_digest == expected_forward_digest")
expect(provider).to_contain(
    "_vulkan_spirv_magic_valid(forward_spirv)")
expect(provider).to_contain(
    "self.forward_spirv, self.inverse_spirv")
expect(provider).to_contain("me warmup() -> text:")
expect(provider).to_contain("self._ensure_ready()")
expect(provider).to_contain(
    "val warmup_reason = self._ensure_ready()")
expect(provider.count("self.session.execute(")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_vulkan_snapshot_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Vulkan SPIR-V snapshot contract.
- X25519MLKEM768 Vulkan SPIR-V snapshot contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
