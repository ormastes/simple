# X25519mlkem768 Metal Warmup Contract Specification

> Tests covering X25519MLKEM768 Metal cold setup contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Metal Warmup Contract Specification

## Scenarios

### X25519MLKEM768 Metal cold setup contract

#### should reject a missing metallib before initializing or dispatching

- Warm a Metal executor whose pinned metallib is missing
   - Expected: executor.session.initialized is false
   - Expected: executor.kernel_invocations equals `0`
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Warm a Metal executor whose pinned metallib is missing")
var executor = X25519MlKem768MetalNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/missing.metallib",
    "0123456789abcdef")
expect(executor.warmup()).to_equal(
    "metal-ntt-binary-artifact-invalid")
expect(executor.session.initialized).to_equal(false)
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should reject a wrong artifact kind before hardware setup

- Warm a Metal binary executor with source instead of a metallib
-  PINNED MSL, file hash sha256
   - Expected: executor.session.initialized is false
   - Expected: executor.kernel_invocations equals `0`
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Warm a Metal binary executor with source instead of a metallib")
var executor = X25519MlKem768MetalNttExecutor.create_binary(
    _PINNED_MSL, file_hash_sha256(_PINNED_MSL))
expect(executor.warmup()).to_equal(
    "metal-ntt-binary-extension-invalid")
expect(executor.session.initialized).to_equal(false)
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should use one idempotent non-dispatch readiness path for warm and lazy setup

- Inspect Metal readiness, byte loading, and the single dispatch path
- "val warmup reason = self  ensure ready
- "self shader = metal sffi load library bytes
- "self shader = metal sffi compile shader
   - Expected: provider.count("self.session.execute(") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect Metal readiness, byte loading, and the single dispatch path")
val provider = file_read_text(
    "src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl")
val session = file_read_text(
    "src/lib/gc_async_mut/crypto_accel/metal_session.spl")
expect(provider).to_contain("me warmup() -> text:")
expect(provider).to_contain("self._ensure_ready()")
expect(provider).to_contain("if not self.session.initialized:")
expect(provider).to_contain(
    "val warmup_reason = self._ensure_ready()")
expect(session).to_contain(
    "self.shader = metal_sffi_load_library_bytes(self.device, artifact_bytes)")
expect(session).to_contain(
    "self.shader = metal_sffi_compile_shader(self.device, source)")
expect(provider.count("self.session.execute(")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_metal_warmup_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Metal cold setup contract.
- X25519MLKEM768 Metal cold setup contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
