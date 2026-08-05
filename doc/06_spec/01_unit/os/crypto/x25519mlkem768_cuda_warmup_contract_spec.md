# X25519mlkem768 Cuda Warmup Contract Specification

> Tests covering X25519MLKEM768 CUDA cold setup contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cuda Warmup Contract Specification

## Scenarios

### X25519MLKEM768 CUDA cold setup contract

#### should fail closed on missing pinned PTX before CUDA access for NFR-012

- Warm a CUDA executor whose pinned PTX artifact is missing
   - Expected: executor.warmup() equals `cuda-ntt-artifact-invalid`
   - Expected: executor.warmup() equals `cuda-ntt-artifact-invalid`
   - Expected: executor.kernel_invocations equals `0`
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Warm a CUDA executor whose pinned PTX artifact is missing")
var executor = X25519MlKem768CudaNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.ptx")
expect(executor.warmup()).to_equal("cuda-ntt-artifact-invalid")
expect(executor.warmup()).to_equal("cuda-ntt-artifact-invalid")
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should fail closed on missing pinned CUBIN before CUDA access for NFR-012

- Warm a CUDA executor whose pinned CUBIN artifact is missing
   - Expected: executor.kernel_invocations equals `0`
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Warm a CUDA executor whose pinned CUBIN artifact is missing")
var executor = X25519MlKem768CudaNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/missing.cubin",
    "0000000000000000000000000000000000000000000000000000000000000000")
expect(executor.warmup()).to_equal(
    "cuda-ntt-binary-artifact-invalid")
expect(executor.warmup()).to_equal(
    "cuda-ntt-binary-artifact-invalid")
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should validate provenance before initialization and load once for NFR-012

- Inspect CUDA warmup ordering, module reuse, and process isolation
- "self session load module
- "val identity = self session identity
- "x25519 mlkem768 cache bind device


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect CUDA warmup ordering, module reuse, and process isolation")
val provider = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val warmup = provider.index_of("me warmup() -> text:")
val warmup_ready = provider.index_of("self._ensure_ready()", warmup)
val ensure_ready = provider.index_of("me _ensure_ready() -> text:")
val binary_digest = provider.index_of(
    "self.artifact_digest != self.expected_artifact_digest",
    ensure_ready)
val source_digest = provider.index_of(
    "self.source_digest != self.expected_source_digest",
    ensure_ready)
val initialize = provider.index_of("self.session.init()", ensure_ready)
val module_guard = provider.index_of(
    "if self.session.module == 0:", ensure_ready)
val module_load = provider.index_of(
    "self.session.load_module(", module_guard)
val device_identity = provider.index_of(
    "val identity = self.session.identity()", module_guard)
val cache_device_bind = provider.index_of(
    "x25519_mlkem768_cache_bind_device(", device_identity)
val execute = provider.index_of("fn _cuda_ntt_execute(")
val launch = provider.index_of("executor.session.launch(", execute)
expect(warmup).to_be_greater_than(0)
expect(warmup_ready).to_be_greater_than(warmup)
expect(binary_digest).to_be_less_than(initialize)
expect(source_digest).to_be_less_than(initialize)
expect(module_guard).to_be_greater_than(initialize)
expect(module_load).to_be_greater_than(module_guard)
expect(device_identity).to_be_greater_than(module_load)
expect(cache_device_bind).to_be_greater_than(device_identity)
expect(launch).to_be_greater_than(execute)
expect(warmup).to_be_less_than(execute)
expect(provider.contains("process_run(")).to_be(false)
expect(provider.contains("rt_process_run")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 CUDA cold setup contract.
- X25519MLKEM768 CUDA cold setup contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
