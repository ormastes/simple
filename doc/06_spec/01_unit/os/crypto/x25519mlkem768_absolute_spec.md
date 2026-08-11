# X25519mlkem768 Absolute Specification

> Tests covering X25519MLKEM768 SIMD static evidence contract, X25519MLKEM768 absolute composition contract, X25519MLKEM768 backend policy, X25519MLKEM768 production entropy boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Absolute Specification

## Scenarios

### X25519MLKEM768 SIMD static evidence contract

#### should pin one cross-backend NTT fixture (REQ-009 REQ-010 REQ-012)

- Compare every backend fixture digest and boundary coefficient
- "x25519mlkem768 ntt fixture coefficient
- "x25519mlkem768 ntt fixture coefficient
- "x25519mlkem768 ntt fixture coefficient
   - Expected: simd_probe does not contain `i * 17 + poly * 101 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare every backend fixture digest and boundary coefficient")
val manifest = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/manifest.sdn")
val simple_fixture = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/canonical_fixture.spl")
val c_fixture = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/ntt_fixture.h")
val simd_probe = file_read_text(
    "test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_c_test.c")
val cuda_probe = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/cuda_ntt_probe.c")
val vulkan_probe = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/vulkan_ntt_probe.c")
val metal_probe = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/metal_ntt_probe.swift")
expect(manifest).to_contain("id: \"ntt-v1-p97-i29-c17-q3329\"")
expect(simple_fixture).to_contain(
    "polynomial * 97 + coefficient * 29 + 17")
expect(c_fixture).to_contain(
    "x25519mlkem768_ntt_fixture_coefficient")
expect(simd_probe).to_contain(
    "x25519mlkem768_ntt_fixture_coefficient(poly, i)")
expect(cuda_probe).to_contain(
    "x25519mlkem768_ntt_fixture_coefficient(p, i)")
expect(vulkan_probe).to_contain(
    "x25519mlkem768_ntt_fixture_coefficient(p, i)")
expect(metal_probe).to_contain(
    "ntt-v1-p97-i29-c17-q3329")
expect(simd_probe.contains("i * 17 + poly * 101 + 3")).to_equal(false)
```

</details>

#### should separate correctness from promotion timing (NFR-009 NFR-010 NFR-011)

- Inspect correctness receipts independently from performance promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect correctness receipts independently from performance promotion")
val simd_runner = file_read_text(
    "scripts/check/check-x25519mlkem768-cpu-simd.shs")
val scalar_runner = file_read_text(
    "scripts/check/check-x25519mlkem768-scalar-perf.shs")
expect(simd_runner).to_contain(
    "mlkem_cpu_simd_correctness_status=pass")
expect(simd_runner).to_contain(
    "mlkem_cpu_simd_performance_status=fail")
expect(simd_runner).to_contain(
    "focused-ntt-speedup-below-threshold")
expect(simd_runner).to_contain(
    "mlkem_cpu_simd_promotion_status=not-proven")
expect(scalar_runner).to_contain(
    "FIXTURE=\"$ROOT/test/fixtures/crypto/x25519mlkem768/canonical_fixture.spl\"")
expect(scalar_runner).to_contain("oracle_fixture_sha256")
```

</details>

#### should keep GNU AVX2 attributes outside the MSVC branch (REQ-009)

- Inspect compiler guards around the AVX2 target attribute
- "#if
- "#  define SIMPLE RUNTIME TARGET AVX2   attribute
   - Expected: source does not contain `\n__attribute__((target("avx2")))\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect compiler guards around the AVX2 target attribute")
val source = file_read_text("src/runtime/runtime_simd_dispatch.c")
expect(source).to_contain(
    "#if (defined(__GNUC__) || defined(__clang__)) && !defined(_MSC_VER)")
expect(source).to_contain(
    "#  define SIMPLE_RUNTIME_TARGET_AVX2 __attribute__((target(\"avx2\")))")
expect(source).to_contain("#  define SIMPLE_RUNTIME_TARGET_AVX2\n")
expect(source.contains("\n__attribute__((target(\"avx2\")))\n")).to_equal(false)
expect(source).to_contain("if (simd_detect_avx2())")
```

</details>

#### should give every ISA evidence row an exact resumable owner contract (REQ-015)

- Validate architecture evidence ownership and resumable commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate architecture evidence ownership and resumable commands")
val manifest = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/manifest.sdn")
expect(manifest).to_contain("MLKEM_SIMD_EXPECTED_BACKEND=1 sh scripts/check/check-x25519mlkem768-cpu-simd.shs")
expect(manifest).to_contain("MLKEM_SIMD_EXPECTED_BACKEND=2 MLKEM_SIMD_RUNNER='qemu-aarch64 -L /usr/aarch64-linux-gnu'")
expect(manifest).to_contain("vlen=128,elen=64")
expect(manifest).to_contain("vlen=256,elen=64")
expect(manifest).to_contain("vlen=512,elen=64")
expect(manifest).to_contain("owner: \"x86_64 AVX2 evidence operator\"")
expect(manifest).to_contain("owner: \"AArch64 NEON evidence operator\"")
expect(manifest).to_contain("owner: \"RISC-V RVV evidence operator\"")
expect(manifest).to_contain(
    "reviewer: \"root Codex normal/highest-capability\"")
```

</details>

### X25519MLKEM768 absolute composition contract

#### should expose the exact immutable versioned profile (REQ-001)

- Read the canonical X25519MLKEM768 profile
   - Expected: profile.fips_revision equals `FIPS 203 ML-KEM-768`
   - Expected: profile.tls_revision equals `draft-ietf-tls-ecdhe-mlkem-05`
   - Expected: profile.named_group equals `0x11EC`
   - Expected: profile.client_share_bytes equals `1216`
   - Expected: profile.server_share_bytes equals `1120`
   - Expected: profile.shared_secret_bytes equals `64`
   - Expected: profile.semantic_version equals `0.3.0`
   - Expected: config.implementation_version equals `0.3.0`
   - Expected: config.minimum_batch equals `1`
- d:  list32
- x25519 private key:  bytes32
   - Expected: request.batch_id equals `absolute-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical X25519MLKEM768 profile")
val profile = x25519_mlkem768_profile()
expect(profile.fips_revision).to_equal("FIPS 203 ML-KEM-768")
expect(profile.tls_revision).to_equal("draft-ietf-tls-ecdhe-mlkem-05")
expect(profile.named_group).to_equal(0x11EC)
expect(profile.client_share_bytes).to_equal(1216)
expect(profile.server_share_bytes).to_equal(1120)
expect(profile.shared_secret_bytes).to_equal(64)
expect(profile.semantic_version).to_equal(
    X25519_MLKEM768_IMPLEMENTATION_VERSION)
expect(profile.semantic_version).to_equal("0.3.0")
val config = x25519_mlkem768_default_config()
expect(config.implementation_version).to_equal("0.3.0")
expect(config.profile_version).to_equal(
    X25519_MLKEM768_PROFILE_VERSION)
expect(config.profile_version).to_equal(
    "fips203-2024+ecdhe-mlkem-05")
expect(config.minimum_batch).to_equal(1)
expect(config.verification_policy ==
    X25519MlKem768VerificationPolicy.AbsoluteAndScalar).to_be(true)
val request = X25519MlKem768Request(
    operation: X25519MlKem768Operation.BatchRoundTrip,
    d: _list32(1), z: _list32(2), m: _list32(3),
    x25519_private_key: _bytes32(4u8), peer_share: [],
    batch_id: "absolute-contract", deterministic_test_input: true)
expect(request.operation ==
    X25519MlKem768Operation.BatchRoundTrip).to_be(true)
expect(request.batch_id).to_equal("absolute-contract")
```

</details>

#### should match NIST ACVP ML-KEM-768 keyGen tcId 26 (REQ-002 REQ-013 REQ-014)

- Run deterministic key generation against the normalized ACVP vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run deterministic key generation against the normalized ACVP vector")
val pair = ml_kem_keygen(_nist_d(), _nist_z())
val (ek, dk) = pair
expect(_bytes_hex(sha256(_list_bytes(ek)))).to_equal(
    "4158f6afb5e516c99f1da07da8c651348422b17c1f4e9a08ad73fb1f91249b3e")
expect(_bytes_hex(sha256(_list_bytes(dk)))).to_equal(
    "7aab35839207f72b310abe36e2daa1cc7ff6f7fa8941e439967cd47d9b437079")
```

</details>

#### should match pinned mlkem-native keygen encapsulation and decapsulation (REQ-002 REQ-013)

- Execute the pinned native oracle keygen encapsulation and decapsulation
- forged[0] = forged get
   - Expected: implicit.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the pinned native oracle keygen encapsulation and decapsulation")
val pair = ml_kem_keygen(_oracle_d(), _oracle_z())
val (ek, dk) = pair
expect(_bytes_hex(sha256(_list_bytes(ek)))).to_equal(
    "c45a699a9efcb1a799578ce95f24b063b0b9ddc0879afdb3967fd9e1e3e8c247")
expect(_bytes_hex(sha256(_list_bytes(dk)))).to_equal(
    "1dc4ab0188bfd90b41bbd91884e40a41ccd0f46e5d3754b615373c9656f6af39")
val encapsulated = ml_kem_encaps(ek, _oracle_d())
val (shared, ciphertext) = encapsulated
expect(_bytes_hex(sha256(_list_bytes(ciphertext)))).to_equal(
    "0b99b2af81971943e4ef6e6f17f42be4f3caa9fea18da0f63df1d43639a74743")
expect(_bytes_hex(sha256(_list_bytes(shared)))).to_equal(
    "340f07be0ffe3d996f44bb05f10eecaca6f494c77a3c353cb1872cacb834f596")
val recovered = ml_kem_decaps(dk, ciphertext)
expect(_bytes_hex(sha256(_list_bytes(recovered)))).to_equal(
    "340f07be0ffe3d996f44bb05f10eecaca6f494c77a3c353cb1872cacb834f596")
var forged = ciphertext
forged[0] = forged.get(0) ^ 1
val implicit = ml_kem_decaps(dk, forged)
expect(implicit.len()).to_equal(32)
expect(_bytes_hex(sha256(_list_bytes(implicit))) ==
    "340f07be0ffe3d996f44bb05f10eecaca6f494c77a3c353cb1872cacb834f596").to_equal(false)
```

</details>

#### should match every byte of the pinned mlkem-native outputs (REQ-002 REQ-012 REQ-013)

- Load the shared X25519MLKEM768 fixture
   - Expected: expected_ek.len() equals `1184`
   - Expected: expected_dk.len() equals `2400`
   - Expected: expected_ct.len() equals `1088`
   - Expected: expected_ss.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the shared X25519MLKEM768 fixture")
val source = file_read_text(
    "test/fixtures/crypto/x25519mlkem768/mlkem_native_fd58_vectors.sdn")
val expected_ek = _hex_list(_fixture_hex_field(
    source, "encapsulation_key_hex"))
val expected_dk = _hex_list(_fixture_hex_field(
    source, "decapsulation_key_hex"))
val expected_ct = _hex_list(_fixture_hex_field(source, "ciphertext_hex"))
val expected_ss = _hex_list(_fixture_hex_field(
    source, "shared_secret_hex"))
expect(expected_ek.len()).to_equal(1184)
expect(expected_dk.len()).to_equal(2400)
expect(expected_ct.len()).to_equal(1088)
expect(expected_ss.len()).to_equal(32)
val pair = ml_kem_keygen(_oracle_d(), _oracle_z())
val (ek, dk) = pair
val encapsulated = ml_kem_encaps(ek, _oracle_d())
val (shared, ciphertext) = encapsulated
val recovered = ml_kem_decaps(dk, ciphertext)
expect(_lists_equal(ek, expected_ek)).to_be(true)
expect(_lists_equal(dk, expected_dk)).to_be(true)
expect(_lists_equal(ciphertext, expected_ct)).to_be(true)
expect(_lists_equal(shared, expected_ss)).to_be(true)
expect(_lists_equal(recovered, expected_ss)).to_be(true)
```

</details>

#### should preserve caller-owned inputs while cleaning owned temporaries (REQ-002 NFR-005)

- Prepare independently owned ML-KEM seeds and message
- Run key generation, encapsulation, and decapsulation
- Verify outputs and every caller-owned input remain intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare independently owned ML-KEM seeds and message")
val d = _oracle_d()
val z = _oracle_z()
val message = _list32(0x5A)
val d_before = _copy_list(d)
val z_before = _copy_list(z)
val message_before = _copy_list(message)

step("Run key generation, encapsulation, and decapsulation")
val pair = match ml_kem_keygen_checked(d, z):
    case Ok(value): value
    case Err(reason): fail(reason)
val (ek, dk) = pair
val ek_before = _copy_list(ek)
val dk_before = _copy_list(dk)
val encapsulated = match ml_kem_encaps_checked(ek, message):
    case Ok(value): value
    case Err(reason): fail(reason)
val (server_secret, ciphertext) = encapsulated
val ciphertext_before = _copy_list(ciphertext)
val client_secret = match ml_kem_decaps_checked(dk, ciphertext):
    case Ok(value): value
    case Err(reason): fail(reason)

step("Verify outputs and every caller-owned input remain intact")
expect(_lists_equal(server_secret, client_secret)).to_be(true)
expect(_lists_equal(d, d_before)).to_be(true)
expect(_lists_equal(z, z_before)).to_be(true)
expect(_lists_equal(message, message_before)).to_be(true)
expect(_lists_equal(ek, ek_before)).to_be(true)
expect(_lists_equal(dk, dk_before)).to_be(true)
expect(_lists_equal(ciphertext, ciphertext_before)).to_be(true)
```

</details>

#### should reject malformed normalized oracle fields (REQ-002)

- Corrupt normalized oracle field lengths before decoding
   - Expected: _fixture_hex_field("other: \"00\"", "missing") equals ``
   - Expected: _fixture_hex_field("value: \"00", "value") equals ``
   - Expected: _hex_list("0").len() equals `0`
   - Expected: _hex_list("0g").len() equals `0`
   - Expected: _hex_list("AF").get(0) equals `175`
   - Expected: _lists_equal([1], [1, 2]) is false
   - Expected: _lists_equal([1, 2], [1, 3]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt normalized oracle field lengths before decoding")
expect(_fixture_hex_field("other: \"00\"", "missing")).to_equal("")
expect(_fixture_hex_field("value: \"00", "value")).to_equal("")
expect(_hex_list("0").len()).to_equal(0)
expect(_hex_list("0g").len()).to_equal(0)
expect(_hex_list("AF").get(0)).to_equal(175)
expect(_lists_equal([1], [1, 2])).to_equal(false)
expect(_lists_equal([1, 2], [1, 3])).to_equal(false)
```

</details>

#### should combine ML-KEM first and X25519 second into 64 bytes (REQ-003 REQ-004)

- Compose the two component secrets in protocol order
   - Expected: secret.len() equals `64`
   - Expected: secret.get(0) equals `0xA5`
   - Expected: secret.get(31) equals `0xA5`
   - Expected: secret.get(32) equals `0x5A`
   - Expected: secret.get(63) equals `0x5A`
   - Expected: reason equals `unexpected composition failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose the two component secrets in protocol order")
val combined = x25519_mlkem768_combine(_list32(0xA5), _bytes32(0x5A))
match combined:
    case Ok(secret):
        expect(secret.len()).to_equal(64)
        expect(secret.get(0)).to_equal(0xA5)
        expect(secret.get(31)).to_equal(0xA5)
        expect(secret.get(32)).to_equal(0x5A)
        expect(secret.get(63)).to_equal(0x5A)
    case Err(reason):
        expect(reason).to_equal("unexpected composition failure")
```

</details>

#### should reject the prohibited all-zero X25519 shared secret (REQ-004 REQ-016 NFR-004)

- Present an all-zero X25519 component to checked composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present an all-zero X25519 component to checked composition")
val combined = x25519_mlkem768_combine(_list32(0xA5), _bytes32(0x00))
match combined:
    case Ok(_): fail("all-zero X25519 secret was accepted")
    case Err(reason): expect(reason).to_contain("all-zero")
```

</details>

#### should reject malformed component lengths (REQ-002 REQ-004 NFR-013)

- Present a malformed ML-KEM component length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present a malformed ML-KEM component length")
val combined = x25519_mlkem768_combine([], _bytes32(0x5A))
match combined:
    case Ok(_): fail("malformed ML-KEM shared secret was accepted")
    case Err(reason): expect(reason).to_contain("32 bytes")
```

</details>

#### should reject a malformed X25519 component length (REQ-002 REQ-004 NFR-013)

- Present a malformed X25519 component length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present a malformed X25519 component length")
val combined = x25519_mlkem768_combine(_list32(0xA5), [])
match combined:
    case Ok(_): fail("malformed X25519 shared secret was accepted")
    case Err(reason): expect(reason).to_contain("32 bytes")
```

</details>

#### should validate canonical ML-KEM keys and reject corruption (REQ-004 NFR-013)

- Validate canonical keys before flipping one encoded byte
   - Expected: ml_kem_768_encapsulation_key_valid(invalid_ek) is false
- invalid dk[2336] = invalid dk get
   - Expected: ml_kem_768_decapsulation_key_valid(invalid_dk) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate canonical keys before flipping one encoded byte")
val pair = ml_kem_keygen(_oracle_d(), _oracle_z())
val (ek, dk) = pair
expect(ml_kem_768_encapsulation_key_valid(ek)).to_be(true)
expect(ml_kem_768_decapsulation_key_valid(dk)).to_be(true)
var invalid_ek = ek
invalid_ek[0] = 0xFF
invalid_ek[1] = 0xFF
expect(ml_kem_768_encapsulation_key_valid(invalid_ek)).to_equal(false)
var invalid_dk = dk
invalid_dk[2336] = invalid_dk.get(2336) ^ 1
expect(ml_kem_768_decapsulation_key_valid(invalid_dk)).to_equal(false)
```

</details>

#### should reject malformed checked ML-KEM inputs (REQ-002 REQ-004 NFR-013)

- Submit malformed key ciphertext and seed lengths to checked APIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit malformed key ciphertext and seed lengths to checked APIs")
match ml_kem_keygen_checked([], _oracle_z()):
    case Ok(_): fail("short ML-KEM d seed was accepted")
    case Err(reason): expect(reason).to_contain("32 bytes")
match ml_kem_keygen_checked(_oracle_d(), []):
    case Ok(_): fail("short ML-KEM z seed was accepted")
    case Err(reason): expect(reason).to_contain("32 bytes")
val pair = ml_kem_keygen(_oracle_d(), _oracle_z())
val (ek, dk) = pair
match ml_kem_encaps_checked(ek, []):
    case Ok(_): fail("short ML-KEM message was accepted")
    case Err(reason): expect(reason).to_contain("32 bytes")
match ml_kem_encaps_checked([], _oracle_d()):
    case Ok(_): fail("short ML-KEM encapsulation key was accepted")
    case Err(reason): expect(reason).to_contain("invalid")
match ml_kem_decaps_checked(dk, []):
    case Ok(_): fail("short ML-KEM ciphertext was accepted")
    case Err(reason): expect(reason).to_contain("1088")
match ml_kem_decaps_checked([], _zero_list(1088)):
    case Ok(_): fail("short ML-KEM decapsulation key was accepted")
    case Err(reason): expect(reason).to_contain("invalid")
```

</details>

#### should reject malformed hybrid public inputs (REQ-003 REQ-004 NFR-013)

- Submit malformed hybrid public-share components
- config, [],  bytes32
- config,  zero list
- config, [],  bytes32
- config,  zero list


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit malformed hybrid public-share components")
val config = x25519_mlkem768_default_config()
match x25519_mlkem768_keygen(config, [], _oracle_d(), _oracle_z()):
    case Ok(_): fail("short hybrid X25519 private key was accepted")
    case Err(reason): expect(reason).to_contain("three 32-byte")
match x25519_mlkem768_keygen(config, _bytes32(1u8), [], _oracle_z()):
    case Ok(_): fail("short hybrid ML-KEM d seed was accepted")
    case Err(reason): expect(reason).to_contain("three 32-byte")
match x25519_mlkem768_encapsulate(
        config, [], _bytes32(1u8), _oracle_d()):
    case Ok(_): fail("short hybrid client share was accepted")
    case Err(reason): expect(reason).to_contain("1216")
match x25519_mlkem768_encapsulate(
        config, _zero_list(1216), [], _oracle_d()):
    case Ok(_): fail("short hybrid server private key was accepted")
    case Err(reason): expect(reason).to_contain("32-byte")
match x25519_mlkem768_decapsulate(
        config, [], _bytes32(1u8), _zero_list(2400)):
    case Ok(_): fail("short hybrid server share was accepted")
    case Err(reason): expect(reason).to_contain("1120")
match x25519_mlkem768_decapsulate(
        config, _zero_list(1120), [], _zero_list(2400)):
    case Ok(_): fail("short hybrid client private key was accepted")
    case Err(reason): expect(reason).to_contain("key sizes")
```

</details>

#### should reject candidate inputs before backend access (REQ-009 REQ-010 NFR-013)

- Exercise candidate input guards with invalid key material
- simd,  empty simd admission
- simd,  empty simd admission
- simd,  empty simd admission
-  zero list
- cuda, cuda executor, [],  oracle d
- cuda, cuda executor, [],  bytes32
- cuda, cuda executor,  zero list
- cuda executor shutdown
- metal, metal executor, [],  oracle d
- metal, metal executor, [],  bytes32
- metal, metal executor,  zero list
- metal executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise candidate input guards with invalid key material")
val simd = _required_candidate_config(X25519MlKem768Backend.Avx2)
match x25519_mlkem768_keygen_simd_candidate(
        simd, _empty_simd_admission(), [], _oracle_d(), _oracle_z()):
    case Ok(_): fail("SIMD accepted a short private key")
    case Err(reason): expect(reason).to_contain("three 32-byte")
match x25519_mlkem768_encapsulate_simd_candidate(
        simd, _empty_simd_admission(), [], _bytes32(1u8), _oracle_d()):
    case Ok(_): fail("SIMD accepted a short client share")
    case Err(reason): expect(reason).to_contain("1216")
match x25519_mlkem768_decapsulate_simd_candidate(
        simd, _empty_simd_admission(), _zero_list(1120), [],
        _zero_list(2400)):
    case Ok(_): fail("SIMD accepted malformed client key material")
    case Err(reason): expect(reason).to_contain("key sizes")

val cuda = _required_candidate_config(X25519MlKem768Backend.Cuda)
var cuda_executor = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
match x25519_mlkem768_keygen_cuda_candidate(
        cuda, cuda_executor, [], _oracle_d(), _oracle_z()):
    case Ok(_): fail("CUDA accepted a short private key")
    case Err(reason): expect(reason).to_contain("three 32-byte")
match x25519_mlkem768_encapsulate_cuda_candidate(
        cuda, cuda_executor, [], _bytes32(1u8), _oracle_d()):
    case Ok(_): fail("CUDA accepted a short client share")
    case Err(reason): expect(reason).to_contain("1216")
match x25519_mlkem768_decapsulate_cuda_candidate(
        cuda, cuda_executor, _zero_list(1120), [], _zero_list(2400)):
    case Ok(_): fail("CUDA accepted malformed client key material")
    case Err(reason): expect(reason).to_contain("key sizes")
cuda_executor.shutdown()

val metal = _required_candidate_config(X25519MlKem768Backend.Metal)
var metal_executor = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
match x25519_mlkem768_keygen_metal_candidate(
        metal, metal_executor, [], _oracle_d(), _oracle_z()):
    case Ok(_): fail("Metal accepted a short private key")
    case Err(reason): expect(reason).to_contain("three 32-byte")
match x25519_mlkem768_encapsulate_metal_candidate(
        metal, metal_executor, [], _bytes32(1u8), _oracle_d()):
    case Ok(_): fail("Metal accepted a short client share")
    case Err(reason): expect(reason).to_contain("1216")
match x25519_mlkem768_decapsulate_metal_candidate(
        metal, metal_executor, _zero_list(1120), [], _zero_list(2400)):
    case Ok(_): fail("Metal accepted malformed client key material")
    case Err(reason): expect(reason).to_contain("key sizes")
metal_executor.shutdown()
```

</details>

### X25519MLKEM768 backend policy

#### should resolve Automatic to the scalar oracle before promotion (REQ-007 REQ-011)

- Resolve Automatic under the unpromoted backend policy
- x25519 mlkem768 default config
   - Expected: evidence.configuration_digest.len() equals `64`
   - Expected: evidence.fallback_used is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve Automatic under the unpromoted backend policy")
val resolved = x25519_mlkem768_resolve_backend(
    x25519_mlkem768_default_config(), "keygen")
match resolved:
    case Ok(evidence):
        expect(evidence.selected_backend == X25519MlKem768Backend.ScalarCpu).to_be(true)
        expect(evidence.requested_backend ==
            X25519MlKem768Backend.Automatic).to_be(true)
        expect(evidence.implementation_version).to_equal(
            X25519_MLKEM768_IMPLEMENTATION_VERSION)
        expect(evidence.profile_version).to_equal(
            X25519_MLKEM768_PROFILE_VERSION)
        expect(evidence.configuration_digest.len()).to_equal(64)
        expect(evidence.fallback_used).to_equal(false)
    case Err(reason): expect(reason).to_equal("unexpected resolver failure")
```

</details>

#### should resolve forced scalar without fallback (REQ-007)

- Require the scalar backend and inspect its selection evidence
   - Expected: evidence.fallback_used is false
   - Expected: evidence.implementation_version equals `0.3.0`
   - Expected: evidence.configuration_digest.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the scalar backend and inspect its selection evidence")
val config = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.ScalarCpu,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(config, "keygen"):
    case Ok(evidence):
        expect(evidence.fallback_used).to_equal(false)
        expect(evidence.implementation_version).to_equal("0.3.0")
        expect(evidence.profile_version).to_equal(
            X25519_MLKEM768_PROFILE_VERSION)
        expect(evidence.configuration_digest.len()).to_equal(64)
    case Err(reason): fail(reason)
```

</details>

#### should reject unsupported API versions and zero batch sizes (REQ-001)

- Present stale versions and invalid batch bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 85 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present stale versions and invalid batch bounds")
val bad_version = X25519MlKem768Config(
    implementation_version: "99.0.0",
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(bad_version, "keygen"):
    case Ok(_): fail("unsupported API version was accepted")
    case Err(reason): expect(reason).to_contain("version")
val legacy_version = X25519MlKem768Config(
    implementation_version: "0.1.0",
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(legacy_version, "keygen"):
    case Ok(_): fail("legacy API version was accepted")
    case Err(reason): expect(reason).to_contain("version")
val bad_profile = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: "99.0.0",
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(bad_profile, "keygen"):
    case Ok(_): fail("unsupported profile version was accepted")
    case Err(reason): expect(reason).to_contain("profile version")
val unsupported_policy = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteOracle,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(unsupported_policy, "keygen"):
    case Ok(_): fail("unsupported verification policy was accepted")
    case Err(reason): expect(reason).to_contain("verification policy")
val bad_batch = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 0
)
match x25519_mlkem768_resolve_backend(bad_batch, "keygen"):
    case Ok(_): fail("zero batch size was accepted")
    case Err(reason): expect(reason).to_contain("positive")
val bad_minimum = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 0,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(bad_minimum, "keygen"):
    case Ok(_): fail("zero minimum batch was accepted")
    case Err(reason): expect(reason).to_contain("minimum_batch")
val below_minimum = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Automatic,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 4,
    batch_size: 3
)
match x25519_mlkem768_resolve_backend(below_minimum, "keygen"):
    case Ok(_): fail("batch below configured minimum was accepted")
    case Err(reason): expect(reason).to_contain("below minimum_batch")
```

</details>

#### should fail closed for a forced unpromoted backend (REQ-007 REQ-008 NFR-013)

- Require an unavailable specialized backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require an unavailable specialized backend")
val config = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Avx2,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 1
)
match x25519_mlkem768_resolve_backend(config, "encapsulate"):
    case Ok(_): fail("unpromoted forced backend was accepted")
    case Err(reason): expect(reason).to_contain("no promoted native implementation")
```

</details>

#### should record an explicit fallback attempt (REQ-007 REQ-008)

- Suggest an unavailable backend and inspect fallback evidence
   - Expected: evidence.attempts.len() equals `2`
   - Expected: evidence.batch_size equals `8`
   - Expected: evidence.implementation_version equals `0.3.0`
   - Expected: evidence.configuration_digest.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Suggest an unavailable backend and inspect fallback evidence")
val config = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Cuda,
    selection_mode: X25519MlKem768SelectionMode.Suggest,
    verification_policy: X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 8
)
match x25519_mlkem768_resolve_backend(config, "encapsulate"):
    case Ok(evidence):
        expect(evidence.fallback_used).to_be(true)
        expect(evidence.requested_backend ==
            X25519MlKem768Backend.Cuda).to_be(true)
        expect(evidence.fallback_reason).to_contain("not promoted")
        expect(evidence.attempts.len()).to_equal(2)
        expect(evidence.batch_size).to_equal(8)
        expect(evidence.implementation_version).to_equal("0.3.0")
        expect(evidence.profile_version).to_equal(
            X25519_MLKEM768_PROFILE_VERSION)
        expect(evidence.configuration_digest.len()).to_equal(64)
    case Err(reason): expect(reason).to_equal("unexpected resolver failure")
```

</details>

### X25519MLKEM768 production entropy boundary

#### should reject invalid entropy request sizes (REQ-016 NFR-006 NFR-013)

- Request entropy below and above the exact supported length
   - Expected: zero_request_candidate[0u64] equals `0u8`
   - Expected: oversized_candidate[0u64] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request entropy below and above the exact supported length")
val zero_request_candidate: [u8] = [0x11u8]
match crypto_entropy_validate_candidate_for_test(
        0u64, true, zero_request_candidate):
    case Ok(_): fail("zero-length entropy request was accepted")
    case Err(reason): expect(reason).to_contain("nonzero")
expect(zero_request_candidate[0u64]).to_equal(0u8)
val oversized_candidate: [u8] = [0x22u8]
match crypto_entropy_validate_candidate_for_test(
        CRYPTO_ENTROPY_MAX_REQUEST + 1u64, true,
        oversized_candidate):
    case Ok(_): fail("oversized entropy request was accepted")
    case Err(reason): expect(reason).to_contain("owner limit")
expect(oversized_candidate[0u64]).to_equal(0u8)
```

</details>

#### should reject malformed entropy providers (REQ-016 NFR-006 NFR-013)

- Return malformed or unauthenticated entropy candidates
   - Expected: unavailable_candidate[0u64] equals `0u8`
   - Expected: short_candidate[0u64] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return malformed or unauthenticated entropy candidates")
val unavailable_candidate: [u8] = _bytes32(1u8)
match crypto_entropy_validate_candidate_for_test(
        32u64, false, unavailable_candidate):
    case Ok(_): fail("unattested entropy provider was accepted")
    case Err(reason): expect(reason).to_contain("unavailable")
expect(unavailable_candidate[0u64]).to_equal(0u8)
val short_candidate: [u8] = [0x33u8]
match crypto_entropy_validate_candidate_for_test(
        32u64, true, short_candidate):
    case Ok(_): fail("wrong-length entropy was accepted")
    case Err(reason): expect(reason).to_contain("wrong length")
expect(short_candidate[0u64]).to_equal(0u8)
```

</details>

#### should accept every attested exact-length byte pattern (REQ-016 NFR-006)

- Accept exact-length candidates without biased output health tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept exact-length candidates without biased output health tests")
match crypto_entropy_validate_candidate_for_test(32u64, true, _bytes32(0xA5u8)):
    case Ok(bytes): expect(bytes.len()).to_equal(32u64)
    case Err(reason): fail(reason)
match crypto_entropy_validate_candidate_for_test(1u64, true, [0u8]):
    case Ok(bytes): expect(bytes[0u64]).to_equal(0u8)
    case Err(reason): fail(reason)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD static evidence contract, X25519MLKEM768 absolute composition contract, X25519MLKEM768 backend policy, X25519MLKEM768 production entropy boundary.
- X25519MLKEM768 SIMD static evidence contract
- X25519MLKEM768 absolute composition contract
- X25519MLKEM768 backend policy
- X25519MLKEM768 production entropy boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
