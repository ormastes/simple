# Backend Dispatch Specification

> <details>

<!-- sdn-diagram:id=backend_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Dispatch Specification

## Scenarios

### backend_dispatch honest GPU/CPU routing

#### cpu target runs the reduce on the CPU reference (ran_on_cpu=true)

- Dispatch reduce on a cpu-scalar target
   - Expected: outcome.value equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch reduce on a cpu-scalar target")
val data = [10, 20, 30]
val outcome = dispatch_reduce_i64(data, 0, add_i64, cpu_target())
expect(outcome.value).to_equal(60)
expect(outcome.stats.ran_on_cpu).to_be(true)
```

</details>

#### gpu-resolved target WITHOUT payload falls back to CPU (no false gpu claim)

- cuda target resolved=true, but no real payload present (forced gate false)
   - Expected: compute_backend_name(cuda_target().backend) equals `cuda`
   - Expected: outcome.stats.backend equals `cuda`
   - Expected: outcome.value equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("cuda target resolved=true, but no real payload present (forced gate false)")
val data = [10, 20, 30]
val outcome = dispatch_reduce_i64_forced(data, 0, add_i64, cuda_target(), false)
# Discriminator: backend is named cuda, target IS a device, yet the CPU ran.
expect(compute_backend_name(cuda_target().backend)).to_equal("cuda")
expect(dispatch_is_device(cuda_target())).to_be(true)
expect(outcome.stats.backend).to_equal("cuda")
expect(outcome.stats.ran_on_cpu).to_be(true)
expect(outcome.value).to_equal(60)
```

</details>

#### gpu-resolved target WITH payload runs on GPU and matches the reference

- cuda target with a real payload present (forced gate true)
   - Expected: gpu_out.stats.backend equals `cuda`
   - Expected: gpu_out.value equals `cpu_out.value`
   - Expected: gpu_out.value equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("cuda target with a real payload present (forced gate true)")
val data = [10, 20, 30]
val gpu_out = dispatch_reduce_i64_forced(data, 0, add_i64, cuda_target(), true)
expect(gpu_out.stats.backend).to_equal("cuda")
# Discriminator: WITH payload, ran_on_cpu flips to false.
expect(gpu_out.stats.ran_on_cpu).to_be(false)
# Differential correctness: GPU value EQUALS the CPU reference value.
val cpu_out = dispatch_reduce_i64_forced(data, 0, add_i64, cuda_target(), false)
expect(gpu_out.value).to_equal(cpu_out.value)
expect(gpu_out.value).to_equal(60)
```

</details>

#### ran_on_cpu DIFFERS between the with-payload and without-payload branches

- Same target, only the payload gate changes
   - Expected: with_payload.value equals `without_payload.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Same target, only the payload gate changes")
val data = [10, 20, 30]
val with_payload = dispatch_reduce_i64_forced(data, 0, add_i64, cuda_target(), true)
val without_payload = dispatch_reduce_i64_forced(data, 0, add_i64, cuda_target(), false)
expect(with_payload.value).to_equal(without_payload.value)
expect(with_payload.stats.ran_on_cpu).to_be(false)
expect(without_payload.stats.ran_on_cpu).to_be(true)
```

</details>

#### gpu_payload_present is exclusive: cuda and metal cannot both be present

- Whatever the env, at most one backend name can match the single payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Whatever the env, at most one backend name can match the single payload")
# Env-agnostic invariant: the gate keys on an exact backend-name match, so
# two distinct names can never both be present.
expect(gpu_payload_present("cuda") and gpu_payload_present("metal")).to_be(false)
```

</details>

#### require-mode: real dispatch_requirement_met TRACKS the real payload gate (env-driven)

- dispatch_requirement_met(cuda) must equal gpu_payload_present(cuda) for a resolved device


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("dispatch_requirement_met(cuda) must equal gpu_payload_present(cuda) for a resolved device")
# This binds the REAL library function to the REAL env path: whatever the
# env says, the requirement signal must agree with the payload gate. With
# SIMPLE_COMPUTE_GPU_PAYLOAD=cuda this is true; without it, false — and the
# assertion still holds because both sides move together. No false claim.
expect(dispatch_requirement_met(cuda_target())).to_be(gpu_payload_present("cuda"))
```

</details>

#### require-mode: real dispatch_requirement_met false when payload mismatches device

- metal target whose name never matches a cuda payload => NOT met


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("metal target whose name never matches a cuda payload => NOT met")
# metal_target is a resolved device; its requirement equals the metal gate.
expect(dispatch_requirement_met(metal_target())).to_be(gpu_payload_present("metal"))
```

</details>

#### require-mode: an unresolved target is never met

- require gpu on a bare machine fails to resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("require gpu on a bare machine fails to resolve")
val unresolved = resolve_exec_target(DeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Require, BackendCaps.none())
expect(unresolved.resolved).to_be(false)
expect(dispatch_requirement_met(unresolved)).to_be(false)
```

</details>

#### cpu target requirement is always met (non-device, no payload needed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch_requirement_met(cpu_target())).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/compute/backend_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- backend_dispatch honest GPU/CPU routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
