# X25519mlkem768 Cache Lifecycle Negative Specification

> Tests covering X25519MLKEM768 cache lifecycle negative branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cache Lifecycle Negative Specification

## Scenarios

### X25519MLKEM768 cache lifecycle negative branches

#### should NFR-012 reject absent provenance and an unbound device

- Attempt admission without provenance and device binding before admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt admission without provenance and device binding before admission")
val absent = x25519_mlkem768_cache_identity("cuda", "", "")
match x25519_mlkem768_cache_bind(
        absent, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("cache accepted absent provenance")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-artifact-identity-invalid")
match x25519_mlkem768_cache_bind_device(absent, 1):
    case Ok(_): fail("cache bound a device before admission")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-unbound")
```

</details>

#### should NFR-012 rebind idempotently and reject invalid devices

- Repeat valid binds and contrast them with zero or changed devices
   - Expected: rebound.admission_digest equals `bound.admission_digest`
   - Expected: rebound.key_digest equals `bound.key_digest`
   - Expected: same_device.key_digest equals `device_bound.key_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Repeat valid binds and contrast them with zero or changed devices")
val bound = _bound_identity()
val rebound = match x25519_mlkem768_cache_bind(
        bound, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(rebound.admission_digest).to_equal(bound.admission_digest)
expect(rebound.key_digest).to_equal(bound.key_digest)
match x25519_mlkem768_cache_bind_device(bound, 0):
    case Ok(_): fail("cache accepted device zero")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-device-invalid")
val device_bound = match x25519_mlkem768_cache_bind_device(bound, 7):
    case Ok(value): value
    case Err(reason): fail(reason)
val same_device = match x25519_mlkem768_cache_bind_device(
        device_bound, 7):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(same_device.key_digest).to_equal(device_bound.key_digest)
```

</details>

#### should NFR-012 reject bound admission-digest corruption

- Mutate the immutable admission digest before rebinding
- var corrupted =  bound identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutate the immutable admission digest before rebinding")
var corrupted = _bound_identity()
corrupted.admission_digest = _OTHER_DIGEST
match x25519_mlkem768_cache_bind(
        corrupted, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("cache accepted corrupted admission identity")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-identity-integrity-mismatch")
```

</details>

#### should reject both bound integrity fields through their independent paths

- Corrupt the execution digest on reuse and admission digest on device bind
- var bad key =  bound identity
- var bad admission =  bound identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt the execution digest on reuse and admission digest on device bind")
var bad_key = _bound_identity()
bad_key.key_digest = _OTHER_DIGEST
match x25519_mlkem768_cache_bind(
        bad_key, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("cache accepted a corrupted execution digest")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-identity-integrity-mismatch")
var bad_admission = _bound_identity()
bad_admission.admission_digest = _OTHER_DIGEST
match x25519_mlkem768_cache_bind_device(bad_admission, 1):
    case Ok(_): fail("cache accepted a corrupted admission digest")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-identity-integrity-mismatch")
```

</details>

#### should NFR-012 reject corrupt index operations without an executor

- Probe invalid hit positions and empty removal paths
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.pop_oldest().backend equals ``
   - Expected: index.remove("cuda", _CONFIG_DIGEST).backend equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe invalid hit positions and empty removal paths")
var index = X25519MlKem768AcceleratorCacheIndex.create(2)
expect(index.validate_hit(-1, _EXECUTION_DIGEST)).to_equal(
    "x25519mlkem768-cache-index-corrupt")
expect(index.validate_hit(0, _EXECUTION_DIGEST)).to_equal(
    "x25519mlkem768-cache-index-corrupt")
expect(index.pop_oldest().backend).to_equal("")
expect(index.remove("cuda", _CONFIG_DIGEST).backend).to_equal("")
```

</details>

#### should NFR-012 reject invalid and duplicate index insertions

- Insert invalid capacities backends keys and a duplicate admission row
- var zero = X25519MlKem768AcceleratorCacheIndex create
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Insert invalid capacities backends keys and a duplicate admission row")
var zero = X25519MlKem768AcceleratorCacheIndex.create(0)
expect(zero.insert(
    "cuda", _CONFIG_DIGEST, _EXECUTION_DIGEST).reason).to_equal(
    "x25519mlkem768-cache-capacity-invalid")
var index = X25519MlKem768AcceleratorCacheIndex.create(2)
expect(index.insert(
    "unknown", _CONFIG_DIGEST, _EXECUTION_DIGEST).reason).to_equal(
    "x25519mlkem768-cache-backend-invalid")
expect(index.insert(
    "cuda", "short", _EXECUTION_DIGEST).reason).to_equal(
    "x25519mlkem768-cache-key-invalid")
expect(index.insert(
    "cuda", _CONFIG_DIGEST, "short").reason).to_equal(
    "x25519mlkem768-cache-key-invalid")
expect(index.insert(
    "cuda", _CONFIG_DIGEST, _EXECUTION_DIGEST).reason).to_equal("")
expect(index.insert(
    "cuda", _CONFIG_DIGEST, _OTHER_DIGEST).reason).to_equal(
    "x25519mlkem768-cache-index-duplicate")
expect(index.remove(
    "cuda", _CONFIG_DIGEST).admission_digest).to_equal(_CONFIG_DIGEST)
expect(index.size()).to_equal(0)
```

</details>

#### should NFR-012 reject all providers after cache shutdown before hardware

- Close the owner before proposing CUDA Metal and Vulkan executors
- cache shutdown
- var cuda = X25519MlKem768CudaNttExecutor create
- var metal = X25519MlKem768MetalNttExecutor create


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close the owner before proposing CUDA Metal and Vulkan executors")
val cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
cache.shutdown()
var cuda = X25519MlKem768CudaNttExecutor.create("missing.ptx")
match cache.admit_cuda(
        cuda, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("closed cache accepted CUDA")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-closed")
expect(cuda.closed).to_be(true)
var metal = X25519MlKem768MetalNttExecutor.create("missing.metal")
match cache.admit_metal(
        metal, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("closed cache accepted Metal")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-closed")
expect(metal.closed).to_be(true)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _SOURCE_DIGEST,
    "missing-inverse.spv", _SOURCE_DIGEST)
match cache.admit_vulkan(
        vulkan, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CONFIG_DIGEST):
    case Ok(_): fail("closed cache accepted Vulkan")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-closed")
expect(vulkan.closed).to_be(true)
```

</details>

#### should retain unknown-completion owners before removing cache metadata

- Inspect transactional GPU eviction invalidation and shutdown ordering
- source index of
- source index of
- source index of
- "self  shutdown eviction
- source index of
   - Expected: cache.quarantined_owner_count() equals `0`
   - Expected: open_retry.attempted equals `0`
   - Expected: open_retry.pending equals `0`
   - Expected: open_retry.vulkan_reason equals `x25519mlkem768-cache-open`
- cache shutdown
   - Expected: cache.quarantined_owner_count() equals `0`
   - Expected: closed_retry.attempted equals `0`
   - Expected: closed_retry.reaped equals `0`
   - Expected: closed_retry.pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect transactional GPU eviction invalidation and shutdown ordering")
val source = file_read_text(
    "src/os/crypto/x25519_mlkem768/accelerator_cache.spl")
val cuda_shutdown = source.index_of("me _shutdown_cuda(")
val metal_shutdown = source.index_of("me _shutdown_metal(")
val vulkan_shutdown = source.index_of("me _shutdown_vulkan(")
val cuda_unknown = source.index_of(
    "if executor.session.completion_unknown:", cuda_shutdown)
val metal_unknown = source.index_of(
    "if executor.session.completion_unknown:", metal_shutdown)
val vulkan_unknown = source.index_of(
    "if executor.session.completion_unknown:", vulkan_shutdown)
expect(cuda_unknown).to_be_less_than(
    source.index_of("self.cuda_entries.remove(index)", cuda_shutdown))
expect(metal_unknown).to_be_less_than(
    source.index_of("self.metal_entries.remove(index)", metal_shutdown))
expect(vulkan_unknown).to_be_less_than(
    source.index_of("self.vulkan_entries.remove(index)", vulkan_shutdown))
val eviction = source.index_of("me _evict_for_admission()")
val eviction_shutdown = source.index_of(
    "self._shutdown_eviction(eviction)", eviction)
val eviction_remove = source.index_of("self.index.remove(", eviction)
expect(eviction_shutdown).to_be_less_than(eviction_remove)
val invalidation = source.index_of("me _invalidate_cuda(")
expect(source.index_of("self._shutdown_cuda(admission_digest)",
    invalidation)).to_be_less_than(
    source.index_of("self.index.remove(\"cuda\"", invalidation))
val cache_shutdown = source.index_of("me shutdown():")
val cache_shutdown_source = source.slice(cache_shutdown, source.len())
expect(cache_shutdown_source.contains("self.cuda_entries = []")).to_be(false)
expect(cache_shutdown_source.contains("self.metal_entries = []")).to_be(false)
expect(cache_shutdown_source.contains("self.vulkan_entries = []")).to_be(false)
val cache = match X25519MlKem768AcceleratorCache.create(1):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(cache.quarantined_owner_count()).to_equal(0)
expect(cache.cleanup_pending()).to_be(false)
val open_retry = cache.retry_quarantined_cleanup()
expect(open_retry.attempted).to_equal(0)
expect(open_retry.pending).to_equal(0)
expect(open_retry.vulkan_reason).to_equal("x25519mlkem768-cache-open")
cache.shutdown()
expect(cache.closed).to_be(true)
expect(cache.quarantined_owner_count()).to_equal(0)
val closed_retry = cache.retry_quarantined_cleanup()
expect(closed_retry.attempted).to_equal(0)
expect(closed_retry.reaped).to_equal(0)
expect(closed_retry.pending).to_equal(0)
expect(closed_retry.cuda_reason).to_equal(
    "cuda-quarantine-not-pending")
expect(closed_retry.metal_reason).to_equal(
    "metal-quarantine-not-pending")
expect(closed_retry.vulkan_reason).to_equal(
    "vulkan-quarantine-not-pending")
```

</details>

#### should retain exact Vulkan dependencies until bounded recovery succeeds

- Inspect ownership transfer retry ordering and unsupported API reasons
- "vulkan sffi quarantine dependencies
- "vulkan sffi quarantine dependencies
- "vulkan sffi recover dependency quarantine


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect ownership transfer retry ordering and unsupported API reasons")
val session_source = file_read_text(
    "src/lib/gc_async_mut/crypto_accel/vulkan_session.spl")
val submit_unknown = session_source.index_of("if fence < 0:")
val submit_transfer = session_source.index_of(
    "vulkan_sffi_quarantine_dependencies(descriptor", submit_unknown)
val submit_terminal = session_source.index_of(
    "self.completion_unknown = true", submit_unknown)
expect(submit_transfer).to_be_less_than(submit_terminal)
val wait_unknown = session_source.index_of("if not completed:")
val retained_fence = session_source.index_of(
    "self.pending_fence = fence", wait_unknown)
val wait_transfer = session_source.index_of(
    "vulkan_sffi_quarantine_dependencies(descriptor", wait_unknown)
expect(retained_fence).to_be_less_than(wait_transfer)
val retry = session_source.index_of("me retry_terminal_completion()")
val recover = session_source.index_of(
    "vulkan_sffi_recover_dependency_quarantine()", retry)
val clear_terminal = session_source.index_of(
    "self.completion_unknown = false", retry)
expect(recover).to_be_less_than(clear_terminal)
val cache_source = file_read_text(
    "src/os/crypto/x25519_mlkem768/accelerator_cache.spl")
expect(cache_source).to_contain(
    "cuda-quarantine-api-gap-context-query-restore-unavailable")
expect(cache_source).to_contain(
    "metal-quarantine-api-gap-command-buffer-handle-unavailable")
expect(cache_source).to_contain("session.retry_terminal_completion()")
```

</details>

#### should NFR-012 reject already-warmed provider state before hardware

- Present preinitialized executors without transferring ownership
- var cuda = X25519MlKem768CudaNttExecutor create
- var metal = X25519MlKem768MetalNttExecutor create
   - Expected: cache.admission_failures equals `3`
- cuda shutdown
- metal shutdown
- vulkan shutdown
- cache shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present preinitialized executors without transferring ownership")
val cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
var cuda = X25519MlKem768CudaNttExecutor.create("missing.ptx")
cuda.device_identity = 1
expect(cache.admit_cuda(
    cuda, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST).is_err()).to_be(true)
var metal = X25519MlKem768MetalNttExecutor.create("missing.metal")
metal.session.initialized = true
expect(cache.admit_metal(
    metal, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST).is_err()).to_be(true)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _SOURCE_DIGEST,
    "missing-inverse.spv", _SOURCE_DIGEST)
vulkan.session.initialized = true
expect(cache.admit_vulkan(
    vulkan, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST).is_err()).to_be(true)
expect(cache.admission_failures).to_equal(3)
cuda.device_identity = 0
metal.session.initialized = false
vulkan.session.initialized = false
cuda.shutdown()
metal.shutdown()
vulkan.shutdown()
cache.shutdown()
```

</details>

#### should NFR-012 reject missing artifacts during provider contract binding

- Bind each provider contract against deliberately absent artifacts
- var cuda = X25519MlKem768CudaNttExecutor create
- cuda shutdown
- var metal = X25519MlKem768MetalNttExecutor create
- metal shutdown
- vulkan shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind each provider contract against deliberately absent artifacts")
var cuda = X25519MlKem768CudaNttExecutor.create("missing.ptx")
expect(cuda.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("cuda-ntt-artifact-invalid")
cuda.shutdown()
var metal = X25519MlKem768MetalNttExecutor.create("missing.metal")
expect(metal.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("metal-ntt-artifact-invalid")
metal.shutdown()
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _SOURCE_DIGEST,
    "missing-inverse.spv", _SOURCE_DIGEST)
expect(vulkan.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("vulkan-ntt-binary-artifact-invalid")
vulkan.shutdown()
```

</details>

#### should reject closed provider bind and warmup paths before hardware

- Close each provider before contract binding and readiness checks
- var cuda = X25519MlKem768CudaNttExecutor create
- cuda shutdown
   - Expected: cuda.warmup() equals `cuda-ntt-executor-closed`
- var metal = X25519MlKem768MetalNttExecutor create
- metal shutdown
   - Expected: metal.warmup() equals `metal-ntt-executor-closed`
- vulkan shutdown
   - Expected: vulkan.warmup() equals `vulkan-ntt-executor-closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close each provider before contract binding and readiness checks")
var cuda = X25519MlKem768CudaNttExecutor.create("missing.ptx")
cuda.shutdown()
expect(cuda.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("cuda-ntt-executor-closed")
expect(cuda.warmup()).to_equal("cuda-ntt-executor-closed")
var metal = X25519MlKem768MetalNttExecutor.create("missing.metal")
metal.shutdown()
expect(metal.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("metal-ntt-executor-closed")
expect(metal.warmup()).to_equal("metal-ntt-executor-closed")
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _SOURCE_DIGEST,
    "missing-inverse.spv", _SOURCE_DIGEST)
vulkan.shutdown()
expect(vulkan.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("vulkan-ntt-executor-closed")
expect(vulkan.warmup()).to_equal("vulkan-ntt-executor-closed")
```

</details>

#### should reject source mismatch extension and uncertain completion before hardware

- Mutate admitted source identities and pre-session lifecycle state
   - Expected: cuda_source.warmup() equals `cuda-ntt-artifact-digest-mismatch`
- cuda source shutdown
- cuda extension shutdown
   - Expected: metal_source.warmup() equals `metal-ntt-artifact-digest-mismatch`
- metal source shutdown
- var uncertain = X25519MlKem768MetalNttExecutor create
   - Expected: uncertain.warmup() equals `metal-session-unavailable`
- uncertain shutdown
   - Expected: vulkan_uncertain.warmup() equals `vulkan-session-unavailable`
- vulkan uncertain shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutate admitted source identities and pre-session lifecycle state")
var cuda_source = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
cuda_source.expected_source_digest = _OTHER_DIGEST
expect(cuda_source.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("cuda-ntt-artifact-digest-mismatch")
expect(cuda_source.warmup()).to_equal("cuda-ntt-artifact-digest-mismatch")
cuda_source.shutdown()
var cuda_extension = X25519MlKem768CudaNttExecutor.create_binary(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx",
    _SOURCE_DIGEST)
expect(cuda_extension.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("cuda-ntt-binary-extension-invalid")
expect(cuda_extension.warmup()).to_equal(
    "cuda-ntt-binary-extension-invalid")
cuda_extension.shutdown()
var metal_source = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
metal_source.expected_source_digest = _OTHER_DIGEST
expect(metal_source.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("metal-ntt-artifact-digest-mismatch")
expect(metal_source.warmup()).to_equal("metal-ntt-artifact-digest-mismatch")
metal_source.shutdown()
var uncertain = X25519MlKem768MetalNttExecutor.create("missing.metal")
uncertain.session.completion_unknown = true
expect(uncertain.warmup()).to_equal("metal-session-unavailable")
expect(uncertain.closed).to_be(true)
expect(uncertain.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("metal-ntt-executor-closed")
uncertain.session.completion_unknown = false
uncertain.shutdown()
var vulkan_uncertain = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _SOURCE_DIGEST,
    "missing-inverse.spv", _SOURCE_DIGEST)
vulkan_uncertain.session.completion_unknown = true
expect(vulkan_uncertain.warmup()).to_equal("vulkan-session-unavailable")
expect(vulkan_uncertain.closed).to_be(true)
expect(vulkan_uncertain.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CONFIG_DIGEST)).to_equal("vulkan-ntt-executor-closed")
vulkan_uncertain.session.completion_unknown = false
vulkan_uncertain.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cache_lifecycle_negative_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 cache lifecycle negative branches.
- X25519MLKEM768 cache lifecycle negative branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
