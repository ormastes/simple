# X25519mlkem768 Cache Contract Specification

> Tests covering X25519MLKEM768 cache boundary contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cache Contract Specification

## Scenarios

### X25519MLKEM768 cache boundary contract

#### should NFR-012 change the configuration digest for every selectable input

- Resolve configurations that differ by exactly one selectable input


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve configurations that differ by exactly one selectable input")
val baseline = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 1))
val backend = _configuration_digest(_cache_config(
    X25519MlKem768Backend.Automatic,
    X25519MlKem768SelectionMode.Suggest, 1, 1))
val selection = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Require, 1, 1))
val minimum_batch = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 2, 2))
val batch_size = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 2))
expect(baseline.len()).to_be_greater_than(0)
expect(backend == baseline).to_be(false)
expect(selection == baseline).to_be(false)
expect(minimum_batch == baseline).to_be(false)
expect(batch_size == baseline).to_be(false)
```

</details>

#### should NFR-012 reject stale semantic and profile versions

- Present stale implementation and profile versions to the resolver


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present stale implementation and profile versions to the resolver")
val current = _cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 1)
val stale_semantic = X25519MlKem768Config(
    implementation_version: "stale-semantic-version",
    profile_version: current.profile_version,
    requested_backend: current.requested_backend,
    selection_mode: current.selection_mode,
    verification_policy: current.verification_policy,
    minimum_batch: current.minimum_batch,
    batch_size: current.batch_size)
val stale_profile = X25519MlKem768Config(
    implementation_version: current.implementation_version,
    profile_version: "stale-profile-version",
    requested_backend: current.requested_backend,
    selection_mode: current.selection_mode,
    verification_policy: current.verification_policy,
    minimum_batch: current.minimum_batch,
    batch_size: current.batch_size)
expect(x25519_mlkem768_resolve_backend(
    stale_semantic, "cache-contract").is_err()).to_be(true)
expect(x25519_mlkem768_resolve_backend(
    stale_profile, "cache-contract").is_err()).to_be(true)
```

</details>

#### should NFR-012 exclude external process launchers from every executor path

- Inspect each backend policy and provider for process launch calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect each backend policy and provider for process launch calls")
val policy = file_read_text(
    "src/os/crypto/x25519_mlkem768/execution_policy.spl")
val cuda = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val vulkan = file_read_text(
    "src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl")
val metal = file_read_text(
    "src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl")
for source in [policy, cuda, vulkan, metal]:
    expect(source.contains("rt_process_run")).to_be(false)
    expect(source.contains("process_run(")).to_be(false)
```

</details>

#### should NFR-012 guard device compilation and module load by session state

- Verify initialization guards precede every backend setup call


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify initialization guards precede every backend setup call")
val cuda = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val metal = file_read_text(
    "src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl")
val vulkan = file_read_text(
    "src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl")
val cuda_guard = cuda.index_of("if self.session.module == 0:")
val cuda_load = cuda.index_of("self.session.load_module(", cuda_guard)
val metal_guard = metal.index_of("if not self.session.initialized:")
val metal_init = metal.index_of("self.session.init(", metal_guard)
val vulkan_guard = vulkan.index_of("if not self.session.initialized:")
val vulkan_init = vulkan.index_of("self.session.init(", vulkan_guard)
expect(cuda_guard).to_be_greater_than(0)
expect(cuda_load).to_be_greater_than(cuda_guard)
expect(metal_guard).to_be_greater_than(0)
expect(metal_init).to_be_greater_than(metal_guard)
expect(vulkan_guard).to_be_greater_than(0)
expect(vulkan_init).to_be_greater_than(vulkan_guard)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 cache boundary contract.
- X25519MLKEM768 cache boundary contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
