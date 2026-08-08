# X25519mlkem768 Backend Matrix Specification

> Tests covering X25519MLKEM768 scalar oracle exchange, X25519MLKEM768 specialized backend promotion boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Backend Matrix Specification

## Scenarios

### X25519MLKEM768 scalar oracle exchange

#### should produce matching scalar client and server secrets (REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-014)

- Run a complete scalar client and server exchange
- config,  byte seed
- config, client client key share,  byte seed
   - Expected: client.client_key_share.len() equals `1216`
   - Expected: server.server_key_share.len() equals `1120`
   - Expected: server.shared_secret.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a complete scalar client and server exchange")
val config = x25519_mlkem768_default_config()
val client = match x25519_mlkem768_keygen(
        config, _byte_seed(1), _list_seed(33), _list_seed(65)):
    case Ok(value): value
    case Err(reason): fail("client key generation failed: {reason}")
val server = match x25519_mlkem768_encapsulate(
        config, client.client_key_share, _byte_seed(97), _list_seed(129)):
    case Ok(value): value
    case Err(reason): fail("server encapsulation failed: {reason}")
val recovered = match x25519_mlkem768_decapsulate(
        config, server.server_key_share, client.x25519_private_key,
        client.decapsulation_key):
    case Ok(value): value
    case Err(reason): fail("client decapsulation failed: {reason}")
expect(client.client_key_share.len()).to_equal(1216)
expect(server.server_key_share.len()).to_equal(1120)
expect(server.shared_secret.len()).to_equal(64)
expect(_lists_equal(server.shared_secret, recovered.shared_secret)).to_be(true)
```

</details>

#### should preserve the portable 1/2/4 provider operation schedule (REQ-010 REQ-012)

- Record keygen encapsulation and decapsulation provider batches
- var provider = RecordingScalarNttProvider create
   - Expected: provider.forward_batches.len() equals `1`
   - Expected: provider.inverse_batches.len() equals `0`
   - Expected: provider.forward_batches.len() equals `2`
   - Expected: provider.inverse_batches.len() equals `1`
   - Expected: provider.forward_batches equals `[6, 3, 3, 3]`
   - Expected: provider.inverse_batches equals `[4, 1, 4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record keygen encapsulation and decapsulation provider batches")
val d = _list_seed(1)
val z = _list_seed(33)
val message = _list_seed(65)
val scalar_pair = match ml_kem_keygen_checked(d, z):
    case Ok(value): value
    case Err(reason): fail(reason)
val (scalar_ek, scalar_dk) = scalar_pair
val scalar_encaps = match ml_kem_encaps_checked(scalar_ek, message):
    case Ok(value): value
    case Err(reason): fail(reason)
val (scalar_shared, scalar_ciphertext) = scalar_encaps
val scalar_decaps = match ml_kem_decaps_checked(
        scalar_dk, scalar_ciphertext):
    case Ok(value): value
    case Err(reason): fail(reason)

var provider = RecordingScalarNttProvider.create()
val provider_pair = match ml_kem_keygen_checked_provider(d, z, provider):
    case Ok(value): value
    case Err(reason): fail(reason)
val (provider_ek, provider_dk) = provider_pair
expect(provider.forward_batches.len()).to_equal(1)
expect(provider.inverse_batches.len()).to_equal(0)
val provider_encaps = match ml_kem_encaps_checked_provider(
        provider_ek, message, provider):
    case Ok(value): value
    case Err(reason): fail(reason)
val (provider_shared, provider_ciphertext) = provider_encaps
expect(provider.forward_batches.len()).to_equal(2)
expect(provider.inverse_batches.len()).to_equal(1)
val provider_decaps = match ml_kem_decaps_checked_provider(
        provider_dk, provider_ciphertext, provider):
    case Ok(value): value
    case Err(reason): fail(reason)

expect(_lists_equal(provider_ek, scalar_ek)).to_be(true)
expect(_lists_equal(provider_dk, scalar_dk)).to_be(true)
expect(_lists_equal(provider_shared, scalar_shared)).to_be(true)
expect(_lists_equal(provider_ciphertext, scalar_ciphertext)).to_be(true)
expect(_lists_equal(provider_decaps, scalar_decaps)).to_be(true)
expect(provider.forward_batches).to_equal([6, 3, 3, 3])
expect(provider.inverse_batches).to_equal([4, 1, 4])
```

</details>

### X25519MLKEM768 specialized backend promotion boundary

#### should give every backend the same NTT fixture (REQ-009 REQ-010 REQ-012)

- Load the canonical NTT fixture shared by all specialized backends
   - Expected: fixture.len() equals `768`
   - Expected: fixture.get(0) equals `17`
   - Expected: fixture.get(256) equals `114`
   - Expected: fixture.get(767) equals `948`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the canonical NTT fixture shared by all specialized backends")
val fixture = _gpu_ntt_fixture(X25519_MLKEM768_NTT_BATCH)
expect(X25519_MLKEM768_NTT_FIXTURE_ID).to_equal(
    "ntt-v1-p97-i29-c17-q3329")
expect(fixture.len()).to_equal(768)
expect(fixture.get(0)).to_equal(17)
expect(fixture.get(256)).to_equal(114)
expect(fixture.get(767)).to_equal(948)
```

</details>

#### should reject invalid candidate resolver configurations (REQ-007 REQ-008 NFR-013)

- Cross-wire backend requests and invalid batch configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cross-wire backend requests and invalid batch configuration")
val zero_batch = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Cuda,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 0)
match x25519_mlkem768_resolve_cuda_candidate(zero_batch, "keygen"):
    case Ok(_): fail("CUDA accepted zero batch size")
    case Err(reason): expect(reason).to_contain("positive")
match x25519_mlkem768_resolve_metal_candidate(zero_batch, "keygen"):
    case Ok(_): fail("Metal accepted zero batch size")
    case Err(reason): expect(reason).to_contain("positive")
match x25519_mlkem768_resolve_simd_candidate(zero_batch, "keygen"):
    case Ok(_): fail("SIMD accepted zero batch size")
    case Err(reason): expect(reason).to_contain("positive")
val bad_version = X25519MlKem768Config(
    implementation_version: "99.0.0",
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Metal,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1)
match x25519_mlkem768_resolve_metal_candidate(
        bad_version, "encapsulate"):
    case Ok(_): fail("Metal accepted an unsupported version")
    case Err(reason): expect(reason).to_contain("version")
match x25519_mlkem768_resolve_cuda_candidate(
        bad_version, "encapsulate"):
    case Ok(_): fail("CUDA accepted an unsupported version")
    case Err(reason): expect(reason).to_contain("version")
match x25519_mlkem768_resolve_simd_candidate(
        bad_version, "encapsulate"):
    case Ok(_): fail("SIMD accepted an unsupported version")
    case Err(reason): expect(reason).to_contain("version")
val wrong_cuda = _candidate_config(X25519MlKem768Backend.Avx2)
match x25519_mlkem768_resolve_cuda_candidate(wrong_cuda, "keygen"):
    case Ok(_): fail("CUDA resolver accepted AVX2")
    case Err(reason): expect(reason).to_contain("not the CUDA")
val wrong_metal = _candidate_config(X25519MlKem768Backend.Rvv)
match x25519_mlkem768_resolve_metal_candidate(wrong_metal, "keygen"):
    case Ok(_): fail("Metal resolver accepted RVV")
    case Err(reason): expect(reason).to_contain("not the Metal")
val scalar = _candidate_config(X25519MlKem768Backend.ScalarCpu)
match x25519_mlkem768_resolve_simd_candidate(scalar, "keygen"):
    case Ok(_): fail("SIMD resolver accepted scalar")
    case Err(reason): expect(reason).to_contain("unavailable")
```

</details>

#### should cover every SIMD selection policy branch deterministically (REQ-009)

- Inject every SIMD backend identity into candidate selection
   - Expected: avx2.selected_backend equals `X25519MlKem768Backend.Avx2`
   - Expected: avx2.executor_identity equals `native-avx2-candidate`
   - Expected: neon.selected_backend equals `X25519MlKem768Backend.Neon`
   - Expected: neon.executor_identity equals `native-neon-candidate`
   - Expected: rvv.selected_backend equals `X25519MlKem768Backend.Rvv`
   - Expected: rvv.executor_identity equals `native-rvv-candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inject every SIMD backend identity into candidate selection")
val avx2 = match _resolve_bound_simd_for_test(
        X25519MlKem768Backend.Avx2, "keygen", 1):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(avx2.selected_backend).to_equal(X25519MlKem768Backend.Avx2)
expect(avx2.executor_identity).to_equal("native-avx2-candidate")
val neon = match _resolve_bound_simd_for_test(
        X25519MlKem768Backend.Neon, "encapsulate", 2):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(neon.selected_backend).to_equal(X25519MlKem768Backend.Neon)
expect(neon.executor_identity).to_equal("native-neon-candidate")
val rvv = match _resolve_bound_simd_for_test(
        X25519MlKem768Backend.Rvv, "decapsulate", 3):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(rvv.selected_backend).to_equal(X25519MlKem768Backend.Rvv)
expect(rvv.executor_identity).to_equal("native-rvv-candidate")
match _resolve_bound_simd_for_test(
        X25519MlKem768Backend.Avx2, "keygen", 2):
    case Ok(_): fail("mismatched injected ISA receipt was accepted")
    case Err(reason): expect(reason).to_contain("unavailable")
```

</details>

#### should match scalar NTT and inverse NTT on every SIMD ISA (REQ-009 REQ-012 NFR-003)

- Run the scalar CPU reference exchange
- Compare SIMD ISA results with the CPU oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the scalar CPU reference exchange")
val polynomial = _gpu_ntt_fixture(1)
val scalar_ntt = ntt(polynomial)
val scalar_roundtrip = intt(scalar_ntt)
step("Compare SIMD ISA results with the CPU oracle")
expect(_lists_equal(ntt_simd(polynomial), scalar_ntt)).to_be(true)
expect(_lists_equal(intt_simd(scalar_ntt), scalar_roundtrip)).to_be(true)
```

</details>

#### should keep full SIMD ML-KEM output byte-identical to scalar (REQ-009 REQ-012)

- Run the scalar CPU reference exchange
- scalar ek,  list seed
- Compare SIMD ISA results with the CPU oracle
-  list seed
- simd ek,  list seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the scalar CPU reference exchange")
val scalar_pair = match ml_kem_keygen_checked(_list_seed(33), _list_seed(65)):
    case Ok(value): value
    case Err(reason): fail(reason)
val (scalar_ek, scalar_dk) = scalar_pair
val scalar_encaps = match ml_kem_encaps_checked(
        scalar_ek, _list_seed(129)):
    case Ok(value): value
    case Err(reason): fail(reason)
val (scalar_shared, scalar_ciphertext) = scalar_encaps
val scalar_decaps = match ml_kem_decaps_checked(
        scalar_dk, scalar_ciphertext):
    case Ok(value): value
    case Err(reason): fail(reason)
step("Compare SIMD ISA results with the CPU oracle")
val simd_pair = match ml_kem_keygen_checked_simd(
        _list_seed(33), _list_seed(65)):
    case Ok(value): value
    case Err(reason): fail(reason)
val (simd_ek, simd_dk) = simd_pair
val simd_encaps = match ml_kem_encaps_checked_simd(
        simd_ek, _list_seed(129)):
    case Ok(value): value
    case Err(reason): fail(reason)
val (simd_shared, simd_ciphertext) = simd_encaps
val simd_decaps = match ml_kem_decaps_checked_simd(
        simd_dk, simd_ciphertext):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(_lists_equal(simd_ek, scalar_ek)).to_be(true)
expect(_lists_equal(simd_dk, scalar_dk)).to_be(true)
expect(_lists_equal(simd_shared, scalar_shared)).to_be(true)
expect(_lists_equal(simd_ciphertext, scalar_ciphertext)).to_be(true)
expect(_lists_equal(simd_decaps, scalar_decaps)).to_be(true)
```

</details>

#### should reject AVX2 without build provenance or on an unavailable host (REQ-009 REQ-015)

- Resolve AVX2 without an admitted Stage-4 build receipt
- avx2,  empty simd admission
-  list seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve AVX2 without an admitted Stage-4 build receipt")
val avx2 = _candidate_config(X25519MlKem768Backend.Avx2)
match x25519_mlkem768_keygen_simd_candidate(
        avx2, _empty_simd_admission(), _byte_seed(1),
        _list_seed(33), _list_seed(65)):
    case Ok(_): fail("AVX2 candidate ran without build provenance")
    case Err(reason):
        if mlkem_ntt_simd_backend() == 1:
            expect(reason).to_contain("Stage-4 build provenance")
        else:
            expect(reason).to_contain("unavailable")
```

</details>

#### should reject NEON without build provenance or on an unavailable host (REQ-009 REQ-015)

- Resolve NEON without an admitted Stage-4 build receipt
- neon,  empty simd admission
-  list seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve NEON without an admitted Stage-4 build receipt")
val neon = _candidate_config(X25519MlKem768Backend.Neon)
match x25519_mlkem768_keygen_simd_candidate(
        neon, _empty_simd_admission(), _byte_seed(1),
        _list_seed(33), _list_seed(65)):
    case Ok(_): fail("NEON candidate ran without build provenance")
    case Err(reason):
        if mlkem_ntt_simd_backend() == 2:
            expect(reason).to_contain("Stage-4 build provenance")
        else:
            expect(reason).to_contain("unavailable")
```

</details>

#### should reject RVV without build provenance or on an unavailable host (REQ-009 REQ-015)

- Resolve RVV without an admitted Stage-4 build receipt
- rvv,  empty simd admission
-  list seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve RVV without an admitted Stage-4 build receipt")
val rvv = _candidate_config(X25519MlKem768Backend.Rvv)
match x25519_mlkem768_keygen_simd_candidate(
        rvv, _empty_simd_admission(), _byte_seed(1),
        _list_seed(33), _list_seed(65)):
    case Ok(_): fail("RVV candidate ran without build provenance")
    case Err(reason):
        if mlkem_ntt_simd_backend() == 3:
            expect(reason).to_contain("Stage-4 build provenance")
        else:
            expect(reason).to_contain("unavailable")
```

</details>

#### should fail closed before AVX2 promotion (REQ-008 REQ-009 REQ-015)

- Require AVX2 through the unpromoted policy boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require AVX2 through the unpromoted policy boundary")
val config = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Avx2,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_keygen(config, _byte_seed(1), _list_seed(33), _list_seed(65)):
    case Ok(_): fail("AVX2 executed without a promoted implementation")
    case Err(reason): expect(reason).to_contain("no promoted native implementation")
```

</details>

#### should fail closed before CUDA promotion (REQ-008 REQ-010 REQ-011)

- Require CUDA through the unpromoted policy boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require CUDA through the unpromoted policy boundary")
val config = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Cuda,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 32
)
match x25519_mlkem768_keygen(config, _byte_seed(1), _list_seed(33), _list_seed(65)):
    case Ok(_): fail("CUDA executed without a promoted implementation")
    case Err(reason): expect(reason).to_contain("no promoted native implementation")
```

</details>

#### should submit and read identical CUDA fixtures (REQ-010 REQ-012 REQ-015 NFR-017)

- Execute forward and inverse CUDA fixtures with device readback
- executor,  gpu ntt fixture
- executor shutdown
   - Expected: forward.kernel_invocations equals `1`
   - Expected: inverse.kernel_invocations equals `1`
   - Expected: forward.completed is false
   - Expected: inverse.completed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute forward and inverse CUDA fixtures with device readback")
var executor = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
val forward = x25519_mlkem768_cuda_ntt_execute(
    executor, _gpu_ntt_fixture(3))
val inverse_input = _gpu_ntt_scalar_expected(3)
val inverse = x25519_mlkem768_cuda_intt_execute(
    executor, inverse_input)
executor.shutdown()
if cuda_available():
    expect(forward.completed).to_be(true)
    expect(forward.compiled).to_be(true)
    expect(forward.submitted).to_be(true)
    expect(forward.fence_completed).to_be(true)
    expect(forward.device_readback).to_be(true)
    expect(forward.kernel_invocations).to_equal(1)
    expect(forward.device_identity).to_be_greater_than(0)
    expect(_lists_equal(forward.values,
        _gpu_ntt_scalar_expected(3))).to_be(true)
    expect(inverse.completed).to_be(true)
    expect(inverse.compiled).to_be(true)
    expect(inverse.submitted).to_be(true)
    expect(inverse.fence_completed).to_be(true)
    expect(inverse.device_readback).to_be(true)
    expect(inverse.kernel_invocations).to_equal(1)
    expect(inverse.device_identity).to_be_greater_than(0)
    expect(_lists_equal(inverse.values,
        _gpu_intt_scalar_expected(inverse_input))).to_be(true)
else:
    expect(forward.completed).to_equal(false)
    expect(forward.reason).to_contain("cuda")
    expect(inverse.completed).to_equal(false)
    expect(inverse.reason).to_contain("cuda")
```

</details>

#### should reject invalid CUDA lifecycle use (REQ-010 NFR-005 NFR-007 NFR-013)

- Exercise invalid CUDA input closed state and artifact admission
   - Expected: empty.completed is false
   - Expected: empty.reason equals `cuda-ntt-input-size-invalid`
- valid shutdown
- valid,  gpu ntt fixture
   - Expected: closed.completed is false
   - Expected: closed.reason equals `cuda-ntt-executor-closed`
- missing,  gpu ntt fixture
   - Expected: invalid.completed is false
   - Expected: invalid.reason equals `cuda-ntt-artifact-invalid`
- missing shutdown
- changed,  gpu ntt fixture
   - Expected: mismatched.completed is false
- changed shutdown
- missing binary,  gpu ntt fixture
   - Expected: absent_binary.completed is false
- missing binary shutdown
- wrong extension,  gpu ntt fixture
   - Expected: rejected_extension.completed is false
- wrong extension shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise invalid CUDA input closed state and artifact admission")
var valid = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
val empty = x25519_mlkem768_cuda_ntt_execute(valid, [])
expect(empty.completed).to_equal(false)
expect(empty.reason).to_equal("cuda-ntt-input-size-invalid")
valid.shutdown()
val closed = x25519_mlkem768_cuda_ntt_execute(
    valid, _gpu_ntt_fixture(1))
expect(closed.completed).to_equal(false)
expect(closed.reason).to_equal("cuda-ntt-executor-closed")
var missing = X25519MlKem768CudaNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.ptx")
val invalid = x25519_mlkem768_cuda_ntt_execute(
    missing, _gpu_ntt_fixture(1))
expect(invalid.completed).to_equal(false)
expect(invalid.reason).to_equal("cuda-ntt-artifact-invalid")
missing.shutdown()
var changed = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
val mismatched = x25519_mlkem768_cuda_ntt_execute(
    changed, _gpu_ntt_fixture(1))
expect(mismatched.completed).to_equal(false)
expect(mismatched.reason).to_equal(
    "cuda-ntt-artifact-digest-mismatch")
changed.shutdown()
var missing_binary = X25519MlKem768CudaNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/missing.cubin",
    "0123456789abcdef")
val absent_binary = x25519_mlkem768_cuda_ntt_execute(
    missing_binary, _gpu_ntt_fixture(1))
expect(absent_binary.completed).to_equal(false)
expect(absent_binary.reason).to_equal(
    "cuda-ntt-binary-artifact-invalid")
missing_binary.shutdown()
var wrong_extension = X25519MlKem768CudaNttExecutor.create_binary(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx",
    "4a40c9895ef9901a7df4f717291ad27b2afb39bb1a4fa26b30409ab2103bf5f6")
val rejected_extension = x25519_mlkem768_cuda_ntt_execute(
    wrong_extension, _gpu_ntt_fixture(1))
expect(rejected_extension.completed).to_equal(false)
expect(rejected_extension.reason).to_equal(
    "cuda-ntt-binary-extension-invalid")
wrong_extension.shutdown()
```

</details>

#### should reject invalid Metal lifecycle use (REQ-010 NFR-005 NFR-007 NFR-013)

- Exercise invalid Metal input closed state and artifact admission
- executor shutdown
- executor,  gpu ntt fixture
- missing,  gpu ntt fixture
- missing shutdown
- changed,  gpu ntt fixture
- changed shutdown
- missing binary,  gpu ntt fixture
- missing binary shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise invalid Metal input closed state and artifact admission")
var executor = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
match x25519_mlkem768_metal_ntt_execute(executor, []):
    case Ok(_): fail("Metal accepted an empty NTT batch")
    case Err(reason): expect(reason).to_equal("metal-ntt-input-size-invalid")
executor.shutdown()
match x25519_mlkem768_metal_intt_execute(
        executor, _gpu_ntt_fixture(1)):
    case Ok(_): fail("Metal executor ran after close")
    case Err(reason): expect(reason).to_equal("metal-ntt-executor-closed")
var missing = X25519MlKem768MetalNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.metal")
match x25519_mlkem768_metal_ntt_execute(
        missing, _gpu_ntt_fixture(1)):
    case Ok(_): fail("Metal accepted a missing artifact")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-artifact-invalid")
missing.shutdown()
var changed = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
match x25519_mlkem768_metal_ntt_execute(
        changed, _gpu_ntt_fixture(1)):
    case Ok(_): fail("Metal accepted an unpinned artifact")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-artifact-digest-mismatch")
changed.shutdown()
var missing_binary = X25519MlKem768MetalNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/missing.metallib",
    "0123456789abcdef")
match x25519_mlkem768_metal_ntt_execute(
        missing_binary, _gpu_ntt_fixture(1)):
    case Ok(_): fail("Metal accepted a missing metallib")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-binary-artifact-invalid")
missing_binary.shutdown()
```

</details>

#### should fail closed in the Vulkan binary provider (REQ-010 REQ-011 NFR-005 NFR-013)

- Exercise Vulkan batch artifact and closed-state guards
- missing,  gpu ntt fixture
- missing shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise Vulkan batch artifact and closed-state guards")
val config = _candidate_config(X25519MlKem768Backend.Vulkan)
match x25519_mlkem768_resolve_vulkan_candidate(config, "keygen"):
    case Ok(evidence):
        expect(evidence.selected_backend).to_equal(
            X25519MlKem768Backend.Vulkan)
        expect(evidence.compiled).to_be(false)
        expect(evidence.submitted).to_be(false)
        expect(evidence.device_readback).to_be(false)
        expect(evidence.oracle_match).to_be(false)
    case Err(reason): fail(reason)
var missing = X25519MlKem768VulkanNttExecutor.create_binaries(
    "test/fixtures/crypto/x25519mlkem768/missing.spv",
    "0123456789abcdef",
    "test/fixtures/crypto/x25519mlkem768/missing_inverse.spv",
    "fedcba9876543210")
match x25519_mlkem768_vulkan_ntt_execute(
        missing, _gpu_ntt_fixture(3)):
    case Ok(_): fail("Vulkan accepted a missing SPIR-V module")
    case Err(reason): expect(reason).to_equal(
        "vulkan-ntt-binary-artifact-invalid")
missing.shutdown()
```

</details>

#### should keep the full CUDA ML-KEM candidate byte-identical to scalar (REQ-010 REQ-012)

- Compare the full CUDA candidate exchange with the scalar oracle
- scalar,  byte seed
-  byte seed
- config, executor,  byte seed
-  list seed
-  byte seed
   - Expected: cuda_client.evidence.kernel_invocations equals `1`
   - Expected: cuda_server.evidence.kernel_invocations equals `2`
   - Expected: cuda_recovered.evidence.kernel_invocations equals `4`
   - Expected: executor.kernel_invocations equals `7`
   - Expected: executor.capacity_bytes equals `6144`
   - Expected: executor.session.generation equals `1`
- executor shutdown
- config, executor,  byte seed
-  list seed
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the full CUDA candidate exchange with the scalar oracle")
val config = _candidate_config(X25519MlKem768Backend.Cuda)
var executor = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
if cuda_available():
    val scalar = x25519_mlkem768_default_config()
    val scalar_client = match x25519_mlkem768_keygen(
            scalar, _byte_seed(1), _list_seed(33), _list_seed(65)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val scalar_server = match x25519_mlkem768_encapsulate(
            scalar, scalar_client.client_key_share,
            _byte_seed(97), _list_seed(129)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val scalar_recovered = match x25519_mlkem768_decapsulate(
            scalar, scalar_server.server_key_share,
            scalar_client.x25519_private_key,
            scalar_client.decapsulation_key):
        case Ok(value): value
        case Err(reason): fail(reason)
    val cuda_client = match x25519_mlkem768_keygen_cuda_candidate(
            config, executor, _byte_seed(1),
            _list_seed(33), _list_seed(65)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val cuda_server = match x25519_mlkem768_encapsulate_cuda_candidate(
            config, executor, cuda_client.client_key_share,
            _byte_seed(97), _list_seed(129)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val cuda_recovered = match x25519_mlkem768_decapsulate_cuda_candidate(
            config, executor, cuda_server.server_key_share,
            cuda_client.x25519_private_key, cuda_client.decapsulation_key):
        case Ok(value): value
        case Err(reason): fail(reason)
    expect(_lists_equal(cuda_client.client_key_share,
        scalar_client.client_key_share)).to_be(true)
    expect(_lists_equal(cuda_server.server_key_share,
        scalar_server.server_key_share)).to_be(true)
    expect(_lists_equal(cuda_server.shared_secret,
        scalar_server.shared_secret)).to_be(true)
    expect(_lists_equal(cuda_recovered.shared_secret,
        cuda_server.shared_secret)).to_be(true)
    expect(cuda_client.evidence.input_fixture_digest).to_equal(
        scalar_client.evidence.input_fixture_digest)
    expect(cuda_server.evidence.input_fixture_digest).to_equal(
        scalar_server.evidence.input_fixture_digest)
    expect(cuda_recovered.evidence.input_fixture_digest).to_equal(
        scalar_recovered.evidence.input_fixture_digest)
    expect(cuda_client.evidence.kernel_invocations).to_equal(1)
    expect(cuda_server.evidence.kernel_invocations).to_equal(2)
    expect(cuda_recovered.evidence.kernel_invocations).to_equal(4)
    expect(cuda_recovered.evidence.fence_completed).to_be(true)
    expect(cuda_recovered.evidence.executor_identity).to_contain(
        "cuda-device:")
    expect(executor.kernel_invocations).to_equal(7)
    expect(executor.capacity_bytes).to_equal(6144)
    expect(executor.session.generation).to_equal(1)
    executor.shutdown()
else:
    match x25519_mlkem768_keygen_cuda_candidate(
            config, executor, _byte_seed(1),
            _list_seed(33), _list_seed(65)):
        case Ok(_): fail("CUDA candidate ran on an unavailable host")
        case Err(reason): expect(reason).to_contain("cuda")
    executor.shutdown()
```

</details>

#### should keep full Metal output identical or report a physical blocker (REQ-010 REQ-012 REQ-015 NFR-017)

- Compare the full Metal candidate exchange or verify its blocker
- scalar,  byte seed
-  byte seed
- config, executor,  byte seed
-  list seed
-  byte seed
   - Expected: metal_client.evidence.kernel_invocations equals `1`
   - Expected: metal_server.evidence.kernel_invocations equals `2`
   - Expected: recovered.evidence.kernel_invocations equals `4`
   - Expected: executor.kernel_invocations equals `7`
   - Expected: executor.session.capacity_bytes equals `6144`
   - Expected: executor.session.generation equals `1`
- executor shutdown
- config, executor,  byte seed
-  list seed
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the full Metal candidate exchange or verify its blocker")
val config = _candidate_config(X25519MlKem768Backend.Metal)
var executor = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
if metal_sffi_is_available():
    val scalar = x25519_mlkem768_default_config()
    val scalar_client = match x25519_mlkem768_keygen(
            scalar, _byte_seed(1), _list_seed(33), _list_seed(65)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val scalar_server = match x25519_mlkem768_encapsulate(
            scalar, scalar_client.client_key_share,
            _byte_seed(97), _list_seed(129)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val scalar_recovered = match x25519_mlkem768_decapsulate(
            scalar, scalar_server.server_key_share,
            scalar_client.x25519_private_key,
            scalar_client.decapsulation_key):
        case Ok(value): value
        case Err(reason): fail(reason)
    val metal_client = match x25519_mlkem768_keygen_metal_candidate(
            config, executor, _byte_seed(1),
            _list_seed(33), _list_seed(65)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val metal_server = match x25519_mlkem768_encapsulate_metal_candidate(
            config, executor, metal_client.client_key_share,
            _byte_seed(97), _list_seed(129)):
        case Ok(value): value
        case Err(reason): fail(reason)
    val recovered = match x25519_mlkem768_decapsulate_metal_candidate(
            config, executor, metal_server.server_key_share,
            metal_client.x25519_private_key, metal_client.decapsulation_key):
        case Ok(value): value
        case Err(reason): fail(reason)
    expect(_lists_equal(metal_client.client_key_share,
        scalar_client.client_key_share)).to_be(true)
    expect(_lists_equal(metal_server.server_key_share,
        scalar_server.server_key_share)).to_be(true)
    expect(_lists_equal(metal_server.shared_secret,
        scalar_server.shared_secret)).to_be(true)
    expect(_lists_equal(recovered.shared_secret,
        metal_server.shared_secret)).to_be(true)
    expect(metal_client.evidence.input_fixture_digest).to_equal(
        scalar_client.evidence.input_fixture_digest)
    expect(metal_server.evidence.input_fixture_digest).to_equal(
        scalar_server.evidence.input_fixture_digest)
    expect(recovered.evidence.input_fixture_digest).to_equal(
        scalar_recovered.evidence.input_fixture_digest)
    expect(metal_client.evidence.kernel_invocations).to_equal(1)
    expect(metal_server.evidence.kernel_invocations).to_equal(2)
    expect(recovered.evidence.kernel_invocations).to_equal(4)
    expect(recovered.evidence.fence_completed).to_be(true)
    expect(executor.kernel_invocations).to_equal(7)
    expect(executor.session.capacity_bytes).to_equal(6144)
    expect(executor.session.generation).to_equal(1)
    executor.shutdown()
else:
    match x25519_mlkem768_keygen_metal_candidate(
            config, executor, _byte_seed(1),
            _list_seed(33), _list_seed(65)):
        case Ok(_): fail("Metal candidate ran on an unavailable host")
        case Err(reason): expect(reason).to_contain("metal")
    executor.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 scalar oracle exchange, X25519MLKEM768 specialized backend promotion boundary.
- X25519MLKEM768 scalar oracle exchange
- X25519MLKEM768 specialized backend promotion boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
