# lowering_aarch64_crypto_spec

> Purpose: Prove that AArch64 cipher intrinsic lowering — AES encrypt rounds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lowering_aarch64_crypto_spec

Purpose: Prove that AArch64 cipher intrinsic lowering — AES encrypt rounds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AArch64 cipher intrinsic lowering — AES encrypt rounds.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AArch64 cipher intrinsic lowering — AES encrypt rounds

#### AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)
- Verify: AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4148284e2168284e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)")
step("Verify: AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)")
# @req: REQ-COMP-AARCH64-CIPHER-INTRINSIC-LOWERING-AES-EN-001
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148284e2168284e")
```

</details>

#### crypto_aes_round output length is 8 bytes

- crypto_aes_round output length is 8 bytes
- Verify: crypto_aes_round output length is 8 bytes
   - Expected: result.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_round output length is 8 bytes")
step("Verify: crypto_aes_round output length is 8 bytes")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

#### AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)

- AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)
- Verify: AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4148284e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)")
step("Verify: AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148284e")
```

</details>

#### crypto_aes_round_last output length is 4 bytes

- crypto_aes_round_last output length is 4 bytes
- Verify: crypto_aes_round_last output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_round_last output length is 4 bytes")
step("Verify: crypto_aes_round_last output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — AES decrypt rounds

#### AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)

- AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)
- Verify: AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4158284e2178284e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)")
step("Verify: AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4158284e2178284e")
```

</details>

#### crypto_aes_inv_round output length is 8 bytes

- crypto_aes_inv_round output length is 8 bytes
- Verify: crypto_aes_inv_round output length is 8 bytes
   - Expected: result.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_inv_round output length is 8 bytes")
step("Verify: crypto_aes_inv_round output length is 8 bytes")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

#### AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)

- AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)
- Verify: AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4158284e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)")
step("Verify: AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4158284e")
```

</details>

#### crypto_aes_inv_round_last output length is 4 bytes

- crypto_aes_inv_round_last output length is 4 bytes
- Verify: crypto_aes_inv_round_last output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_inv_round_last output length is 4 bytes")
step("Verify: crypto_aes_inv_round_last output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — SHA-256

#### SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)

- SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)
- Verify: SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4140035e4150035e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)")
step("Verify: SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)")
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4140035e4150035e")
```

</details>

#### crypto_sha256_rnds2 output length is 8 bytes

- crypto_sha256_rnds2 output length is 8 bytes
- Verify: crypto_sha256_rnds2 output length is 8 bytes
   - Expected: result.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_sha256_rnds2 output length is 8 bytes")
step("Verify: crypto_sha256_rnds2 output length is 8 bytes")
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

### AArch64 cipher intrinsic lowering — CRC32

#### CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)

- CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)
- Verify: CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4140c31a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)")
step("Verify: CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4140c31a")
```

</details>

#### crc32_u8 output length is 4 bytes

- crc32_u8 output length is 4 bytes
- Verify: crc32_u8 output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u8 output length is 4 bytes")
step("Verify: crc32_u8 output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)

- CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)
- Verify: CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `4148c31a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)")
step("Verify: CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("crc32_u32", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148c31a")
```

</details>

#### crc32_u32 output length is 4 bytes

- crc32_u32 output length is 4 bytes
- Verify: crc32_u32 output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u32 output length is 4 bytes")
step("Verify: crc32_u32 output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("crc32_u32", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)

- CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)
- Verify: CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `414cc39a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)")
step("Verify: CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("crc32_u64", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("414cc39a")
```

</details>

#### crc32_u64 output length is 4 bytes

- crc32_u64 output length is 4 bytes
- Verify: crc32_u64 output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u64 output length is 4 bytes")
step("Verify: crc32_u64 output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("crc32_u64", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — CLMUL (PMULL)

#### PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)

- PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)
- Verify: PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `41e0e30e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)")
step("Verify: PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("clmul_lo", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("41e0e30e")
```

</details>

#### clmul_lo output length is 4 bytes

- clmul_lo output length is 4 bytes
- Verify: clmul_lo output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clmul_lo output length is 4 bytes")
step("Verify: clmul_lo output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("clmul_lo", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)

- PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)
- Verify: PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `41e0e34e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)")
step("Verify: PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)")
val result = lower_cipher_intrinsic_aarch64("clmul_hi", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("41e0e34e")
```

</details>

#### clmul_hi output length is 4 bytes

- clmul_hi output length is 4 bytes
- Verify: clmul_hi output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clmul_hi output length is 4 bytes")
step("Verify: clmul_hi output length is 4 bytes")
val result = lower_cipher_intrinsic_aarch64("clmul_hi", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — failure cases

#### unknown intrinsic returns lowered=false, reason=unknown

- unknown intrinsic returns lowered=false, reason=unknown
- Verify: unknown intrinsic returns lowered=false, reason=unknown
   - Expected: result.lowered is false
   - Expected: result.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown intrinsic returns lowered=false, reason=unknown")
step("Verify: unknown intrinsic returns lowered=false, reason=unknown")
val result = lower_cipher_intrinsic_aarch64("unknown_intrinsic", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("unknown")
```

</details>

#### crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity

- crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity
- Verify: crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity
   - Expected: result.lowered is false
   - Expected: result.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity")
step("Verify: crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity")
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity

- crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity
- Verify: crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity
   - Expected: result.lowered is false
   - Expected: result.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity")
step("Verify: crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity")
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

#### crc32_u8 with 2 args returns lowered=false, reason=bad-arity

- crc32_u8 with 2 args returns lowered=false, reason=bad-arity
- Verify: crc32_u8 with 2 args returns lowered=false, reason=bad-arity
   - Expected: result.lowered is false
   - Expected: result.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u8 with 2 args returns lowered=false, reason=bad-arity")
step("Verify: crc32_u8 with 2 args returns lowered=false, reason=bad-arity")
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-AARCH64-CIPHER-INTRINSIC-LOWERING-AES-EN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4792c3c6bdde8a9fba0ec245f6cee7f4571644606be9e3355f256274d0ab3a3a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4792c3c6bdde8a9fba0ec245f6cee7f4571644606be9e3355f256274d0ab3a3a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4792c3c6bdde8a9fba0ec245f6cee7f4571644606be9e3355f256274d0ab3a3a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl
mirror: doc/06_spec/unit/compiler/backend/lowering_aarch64_crypto_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/lowering_aarch64_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/lowering_aarch64_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round output length is 8 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/lowering_aarch64_crypto_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
