# X25519mlkem768 Accelerator Cache Specification

> Tests covering X25519MLKEM768 accelerator executor cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Accelerator Cache Specification

## Scenarios

### X25519MLKEM768 accelerator executor cache

#### should REQ-NFR012-01 keep admission and execution identities distinct

- Probe an empty cache with the immutable admission digest
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.probe("cuda", _KEY_A) equals `-1`
   - Expected: index.misses equals `1`
- Record the warmed device-bound execution digest
   - Expected: inserted.reason equals ``
   - Expected: index.size() equals `1`
   - Expected: index.entries.get(0).admission_digest equals `_KEY_A`
   - Expected: index.entries.get(0).execution_digest equals `_EXEC_A`
- Resolve the pre-warmup admission key as a validated hit
   - Expected: hit_index equals `0`
   - Expected: index.validate_hit(hit_index, _EXEC_A) equals ``
   - Expected: index.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe an empty cache with the immutable admission digest")
var index = X25519MlKem768AcceleratorCacheIndex.create(2)
expect(index.probe("cuda", _KEY_A)).to_equal(-1)
expect(index.misses).to_equal(1)

step("Record the warmed device-bound execution digest")
val inserted = index.insert("cuda", _KEY_A, _EXEC_A)
expect(inserted.reason).to_equal("")
expect(index.size()).to_equal(1)
expect(index.entries.get(0).admission_digest).to_equal(_KEY_A)
expect(index.entries.get(0).execution_digest).to_equal(_EXEC_A)

step("Resolve the pre-warmup admission key as a validated hit")
val hit_index = index.probe("cuda", _KEY_A)
expect(hit_index).to_equal(0)
expect(index.validate_hit(hit_index, _EXEC_A)).to_equal("")
expect(index.hits).to_equal(1)
```

</details>

#### should REQ-NFR012-02 reject execution identity drift on a hit

- Seed one admitted execution identity
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.insert("metal", _KEY_A, _EXEC_A).reason equals ``
- Present a different post-warmup execution identity
   - Expected: index.hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed one admitted execution identity")
var index = X25519MlKem768AcceleratorCacheIndex.create(1)
expect(index.insert("metal", _KEY_A, _EXEC_A).reason).to_equal("")

step("Present a different post-warmup execution identity")
val hit_index = index.probe("metal", _KEY_A)
expect(index.validate_hit(hit_index, _EXEC_B)).to_equal(
    "x25519mlkem768-cache-execution-key-mismatch")
expect(index.hits).to_equal(0)
```

</details>

#### should REQ-NFR012-02 reject non-hex index identities

- Present a 64-character value outside the SHA-256 hex alphabet
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present a 64-character value outside the SHA-256 hex alphabet")
var index = X25519MlKem768AcceleratorCacheIndex.create(1)
val not_hex =
    "gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg"
expect(index.insert("cuda", not_hex, _EXEC_A).reason).to_equal(
    "x25519mlkem768-cache-key-invalid")
expect(index.size()).to_equal(0)
```

</details>

#### should REQ-NFR012-03 evict globally in deterministic FIFO order

- Fill a two-entry cache in CUDA then Metal order
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.insert("cuda", _KEY_A, _EXEC_A).reason equals ``
   - Expected: index.insert("metal", _KEY_B, _EXEC_B).reason equals ``
- Hit CUDA without changing deterministic insertion order
   - Expected: index.validate_hit(hit_index, _EXEC_A) equals ``
- Admit Vulkan and inspect the exact oldest eviction
   - Expected: inserted.reason equals ``
   - Expected: inserted.eviction.backend equals `cuda`
   - Expected: inserted.eviction.admission_digest equals `_KEY_A`
   - Expected: index.size() equals `2`
   - Expected: index.evictions equals `1`
   - Expected: index.entries.get(0).backend equals `metal`
   - Expected: index.entries.get(1).backend equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill a two-entry cache in CUDA then Metal order")
var index = X25519MlKem768AcceleratorCacheIndex.create(2)
expect(index.insert("cuda", _KEY_A, _EXEC_A).reason).to_equal("")
expect(index.insert("metal", _KEY_B, _EXEC_B).reason).to_equal("")

step("Hit CUDA without changing deterministic insertion order")
val hit_index = index.probe("cuda", _KEY_A)
expect(index.validate_hit(hit_index, _EXEC_A)).to_equal("")

step("Admit Vulkan and inspect the exact oldest eviction")
val inserted = index.insert("vulkan", _KEY_C, _EXEC_C)
expect(inserted.reason).to_equal("")
expect(inserted.eviction.backend).to_equal("cuda")
expect(inserted.eviction.admission_digest).to_equal(_KEY_A)
expect(index.size()).to_equal(2)
expect(index.evictions).to_equal(1)
expect(index.entries.get(0).backend).to_equal("metal")
expect(index.entries.get(1).backend).to_equal("vulkan")
```

</details>

#### should REQ-NFR012-04 reject zero and excessive capacities

- Create owners outside the bounded capacity contract
- Create and deterministically close an empty bounded owner
   - Expected: cache.size() equals `0`
- cache shutdown
   - Expected: cache.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create owners outside the bounded capacity contract")
match X25519MlKem768AcceleratorCache.create(0):
    case Ok(_): fail("cache accepted zero capacity")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-capacity-invalid")
match X25519MlKem768AcceleratorCache.create(65):
    case Ok(_): fail("cache accepted excessive capacity")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-capacity-invalid")

step("Create and deterministically close an empty bounded owner")
match X25519MlKem768AcceleratorCache.create(2):
    case Err(reason): fail(reason)
    case Ok(cache):
        expect(cache.size()).to_equal(0)
        cache.shutdown()
        expect(cache.closed).to_equal(true)
```

</details>

#### should REQ-NFR012-05 warm every backend before retaining or returning it

- Inspect the pure-Simple feature owner contract
   - Expected: source.count("val warmup_reason = retained.warmup()") equals `3`
   - Expected: source.count("val warmup_reason = executor.warmup()") equals `3`
   - Expected: source.count("execution_digest: executor.cache_identity.key_digest") equals `3`
   - Expected: source.count(", \"cache-admission\")") equals `3`
   - Expected: source does not contain `process_run`
   - Expected: source does not contain `secret: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the pure-Simple feature owner contract")
val source = file_read_text(
    "src/os/crypto/x25519_mlkem768/accelerator_cache.spl")
expect(source.count("val warmup_reason = retained.warmup()")).to_equal(3)
expect(source.count("val warmup_reason = executor.warmup()")).to_equal(3)
expect(source.count("execution_digest: executor.cache_identity.key_digest")).to_equal(3)
expect(source).to_contain(
    "val admission_digest = executor.cache_identity.admission_digest")
expect(source.count(
    "x25519mlkem768-cache-input-already-warmed")).to_equal(3)
expect(source).to_contain("me admit_cuda_config(")
expect(source).to_contain("me admit_metal_config(")
expect(source).to_contain("me admit_vulkan_config(")
expect(source.count(", \"cache-admission\")")).to_equal(3)
expect(source.contains("process_run")).to_equal(false)
expect(source.contains("secret: text")).to_equal(false)
```

</details>

#### should REQ-NFR012-06 reject mismatched typed configs before hardware

- Cross-wire typed backend configurations before provider warmup
- cuda,  cache config
- metal,  cache config
- vulkan,  cache config
   - Expected: cache.admission_failures equals `3`
   - Expected: cache.size() equals `0`
- cache shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cross-wire typed backend configurations before provider warmup")
val cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
var cuda = X25519MlKem768CudaNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.ptx")
match cache.admit_cuda_config(
        cuda, _cache_config(X25519MlKem768Backend.Metal)):
    case Ok(_): fail("CUDA cache accepted a Metal configuration")
    case Err(reason): expect(reason).to_contain("not the CUDA candidate")
expect(cuda.closed).to_be(true)
var metal = X25519MlKem768MetalNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.metal")
match cache.admit_metal_config(
        metal, _cache_config(X25519MlKem768Backend.Cuda)):
    case Ok(_): fail("Metal cache accepted a CUDA configuration")
    case Err(reason): expect(reason).to_contain("not the Metal candidate")
expect(metal.closed).to_be(true)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "", "missing-inverse.spv", "")
match cache.admit_vulkan_config(
        vulkan, _cache_config(X25519MlKem768Backend.Cuda)):
    case Ok(_): fail("Vulkan cache accepted a CUDA configuration")
    case Err(reason): expect(reason).to_contain("not the Vulkan candidate")
expect(vulkan.closed).to_be(true)
expect(cache.admission_failures).to_equal(3)
expect(cache.size()).to_equal(0)
cache.shutdown()
```

</details>

#### should REQ-NFR012-07 preserve ownership before config resolution and eviction

- Reject an index whose public capacity no longer matches its rows
- var index = X25519MlKem768AcceleratorCacheIndex create
   - Expected: index.insert("cuda", _KEY_A, _EXEC_A).reason equals ``
   - Expected: index.insert("metal", _KEY_B, _EXEC_B).reason equals ``
   - Expected: index.size() equals `2`
   - Expected: index.evictions equals `0`
- Inspect ownership guards and eviction preflight ordering
- " proposal ownership reason
   - Expected: source.count("val _removed_corrupt = self.index.remove(") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an index whose public capacity no longer matches its rows")
var index = X25519MlKem768AcceleratorCacheIndex.create(2)
expect(index.insert("cuda", _KEY_A, _EXEC_A).reason).to_equal("")
expect(index.insert("metal", _KEY_B, _EXEC_B).reason).to_equal("")
index.capacity = 1
expect(index.insert("vulkan", _KEY_C, _EXEC_C).reason).to_equal(
    "x25519mlkem768-cache-index-corrupt")
expect(index.size()).to_equal(2)
expect(index.evictions).to_equal(0)

step("Inspect ownership guards and eviction preflight ordering")
val source = file_read_text(
    "src/os/crypto/x25519_mlkem768/accelerator_cache.spl")
for backend in ["cuda", "metal", "vulkan"]:
    val config_start = source.index_of("me admit_{backend}_config(")
    val next_method = source.index_of("\n    me ", config_start + 1)
    val config_body = source.slice(config_start, next_method)
    val ownership_guard = config_body.index_of(
        "_proposal_ownership_reason(executor)")
    val resolver = config_body.index_of(
        "x25519_mlkem768_resolve_{backend}_candidate")
    expect(ownership_guard).to_be_greater_than(-1)
    expect(resolver).to_be_greater_than(ownership_guard)
expect(source.count(
    "val eviction_ready_reason = self._eviction_ready_reason()")).to_equal(3)
expect(source.count("val _removed_corrupt = self.index.remove(")).to_equal(3)
```

</details>

#### should REQ-NFR012-08 remove typed-index divergence before hardware access

- Seed a CUDA index hit without its typed retained executor
   - Expected: cuda_cache.size() equals `0`
   - Expected: cuda_cache.admission_failures equals `1`
- cuda cache shutdown
- Seed a Metal index hit without its typed retained executor
   - Expected: metal_cache.size() equals `0`
   - Expected: metal_cache.admission_failures equals `1`
- metal cache shutdown
- Seed a Vulkan index hit without its typed retained executor
   - Expected: vulkan_cache.size() equals `0`
   - Expected: vulkan_cache.admission_failures equals `1`
- vulkan cache shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed a CUDA index hit without its typed retained executor")
val cuda_cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
var cuda = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
cuda.expected_source_digest = cuda.source_digest
expect(cuda.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION, _KEY_A)).to_equal("")
val cuda_admission = cuda.cache_identity.admission_digest
expect(cuda_cache.index.insert(
    "cuda", cuda_admission, cuda.cache_identity.key_digest).reason).to_equal("")
match cuda_cache.admit_cuda(
        cuda, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _KEY_A):
    case Ok(_): fail("CUDA cache accepted typed-index divergence")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-index-corrupt")
expect(cuda.closed).to_be(true)
expect(cuda_cache.size()).to_equal(0)
expect(cuda_cache.admission_failures).to_equal(1)
cuda_cache.shutdown()

step("Seed a Metal index hit without its typed retained executor")
val metal_cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
var metal = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
metal.expected_source_digest = metal.source_digest
expect(metal.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION, _KEY_B)).to_equal("")
val metal_admission = metal.cache_identity.admission_digest
expect(metal_cache.index.insert(
    "metal", metal_admission, metal.cache_identity.key_digest).reason).to_equal("")
match metal_cache.admit_metal(
        metal, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _KEY_B):
    case Ok(_): fail("Metal cache accepted typed-index divergence")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-index-corrupt")
expect(metal.closed).to_be(true)
expect(metal_cache.size()).to_equal(0)
expect(metal_cache.admission_failures).to_equal(1)
metal_cache.shutdown()

step("Seed a Vulkan index hit without its typed retained executor")
val vulkan_cache = match X25519MlKem768AcceleratorCache.create(2):
    case Ok(value): value
    case Err(reason): fail(reason)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", _KEY_A,
    "missing-inverse.spv", _KEY_B)
vulkan.admission_reason = ""
vulkan.cache_identity = x25519_mlkem768_cache_identity(
    "vulkan", "", _KEY_C)
expect(vulkan.bind_cache_contract(
    X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION, _KEY_C)).to_equal("")
val vulkan_admission = vulkan.cache_identity.admission_digest
expect(vulkan_cache.index.insert(
    "vulkan", vulkan_admission,
    vulkan.cache_identity.key_digest).reason).to_equal("")
match vulkan_cache.admit_vulkan(
        vulkan, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _KEY_C):
    case Ok(_): fail("Vulkan cache accepted typed-index divergence")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-index-corrupt")
expect(vulkan.closed).to_be(true)
expect(vulkan_cache.size()).to_equal(0)
expect(vulkan_cache.admission_failures).to_equal(1)
vulkan_cache.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_accelerator_cache_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 accelerator executor cache.
- X25519MLKEM768 accelerator executor cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
