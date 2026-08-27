# OS Crypto Random Reference Comparison

> Small deterministic randomized comparison tests for the hosted security

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OS Crypto Random Reference Comparison

Small deterministic randomized comparison tests for the hosted security

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_crypto_random_ref_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Small deterministic randomized comparison tests for the hosted security
primitive surface. Inputs are generated in-process, then Simple outputs are
compared with the existing Python and Node reference modules.

## Scenarios

### os_crypto_random_ref: hash and MAC random input comparison

#### SHA-256 matches Python and Node for randomized byte shapes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SHA-256 matches Python and Node for randomized byte shapes
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SHA-256 matches Python and Node for randomized byte shapes")
_seed(0x1234)
var i: u64 = 0
while i < 16:
    val msg = _random_bytes((i * 13) % 129)
    val simple = bytes_to_hex(sha256(msg))
    val py = bytes_to_hex(_unwrap_bytes(ref_sha256_via(Vendor.PYTHON, msg)))
    val node = bytes_to_hex(_unwrap_bytes(ref_sha256_via(Vendor.NODE, msg)))
    expect(simple).to_equal(py)
    expect(simple).to_equal(node)
    i = i + 1
```

</details>

#### SHA-512 matches Python and Node for randomized byte shapes

- SHA-512 matches Python and Node for randomized byte shapes
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SHA-512 matches Python and Node for randomized byte shapes")
_seed(0x5678)
var i: u64 = 0
while i < 12:
    val msg = _random_bytes((i * 17) % 161)
    val simple = bytes_to_hex(sha512(msg))
    val py = bytes_to_hex(_unwrap_bytes(ref_sha512_via(Vendor.PYTHON, msg)))
    val node = bytes_to_hex(_unwrap_bytes(ref_sha512_via(Vendor.NODE, msg)))
    expect(simple).to_equal(py)
    expect(simple).to_equal(node)
    i = i + 1
```

</details>

#### HMAC-SHA256 matches Python and Node for randomized keys and messages

- HMAC-SHA256 matches Python and Node for randomized keys and messages
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HMAC-SHA256 matches Python and Node for randomized keys and messages")
_seed(0x9abc)
var i: u64 = 0
while i < 16:
    val key = _random_bytes(1 + ((i * 11) % 96))
    val msg = _random_bytes((i * 19) % 143)
    val simple = bytes_to_hex(sha256_hmac(key, msg))
    val py = bytes_to_hex(_unwrap_bytes(ref_hmac_sha256_via(Vendor.PYTHON, key, msg)))
    val node = bytes_to_hex(_unwrap_bytes(ref_hmac_sha256_via(Vendor.NODE, key, msg)))
    expect(simple).to_equal(py)
    expect(simple).to_equal(node)
    i = i + 1
```

</details>

### os_crypto_random_ref: AEAD random input comparison

#### AES-128-GCM encrypt/decrypt matches Python and Node

- AES-128-GCM encrypt/decrypt matches Python and Node
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(py)`
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(node)`
   - Expected: _aes128_decrypt_ok(key, nonce, aad, py, plain) is true
   - Expected: _bytes_eq(_unwrap_bytes(ref_aes_128_gcm_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AES-128-GCM encrypt/decrypt matches Python and Node")
_seed(0x2468)
var i: u64 = 0
while i < 10:
    val key = _random_bytes(16)
    val nonce = _random_bytes(12)
    val aad = _random_bytes((i * 7) % 31)
    val plain = _random_bytes((i * 23) % 97)
    val simple = aes128_gcm_encrypt(key, nonce, plain, aad)
    val py = _unwrap_bytes(ref_aes_128_gcm_encrypt_via(Vendor.PYTHON, key, nonce, aad, plain))
    val node = _unwrap_bytes(ref_aes_128_gcm_encrypt_via(Vendor.NODE, key, nonce, aad, plain))
    expect(bytes_to_hex(simple)).to_equal(bytes_to_hex(py))
    expect(bytes_to_hex(simple)).to_equal(bytes_to_hex(node))
    expect(_aes128_decrypt_ok(key, nonce, aad, py, plain)).to_equal(true)
    expect(_bytes_eq(_unwrap_bytes(ref_aes_128_gcm_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain)).to_equal(true)
    i = i + 1
```

</details>

#### ChaCha20-Poly1305 encrypt/decrypt matches Python and Node

- ChaCha20-Poly1305 encrypt/decrypt matches Python and Node
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(py)`
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(node)`
   - Expected: _chacha_decrypt_ok(key, nonce, aad, py, plain) is true
   - Expected: _bytes_eq(_unwrap_bytes(ref_chacha_poly_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ChaCha20-Poly1305 encrypt/decrypt matches Python and Node")
_seed(0x1357)
var i: u64 = 0
while i < 14:
    val key = _random_bytes(32)
    val nonce = _random_bytes(12)
    val aad = _random_bytes((i * 5) % 29)
    val plain_len = if i == 10: 114u64 else: ((i * 17) % 181)
    val plain = _random_bytes(plain_len)
    val simple = chacha20_poly1305_encrypt(key, nonce, plain, aad)
    val py = _unwrap_bytes(ref_chacha_poly_encrypt_via(Vendor.PYTHON, key, nonce, aad, plain))
    val node = _unwrap_bytes(ref_chacha_poly_encrypt_via(Vendor.NODE, key, nonce, aad, plain))
    expect(bytes_to_hex(simple)).to_equal(bytes_to_hex(py))
    expect(bytes_to_hex(simple)).to_equal(bytes_to_hex(node))
    expect(_chacha_decrypt_ok(key, nonce, aad, py, plain)).to_equal(true)
    expect(_bytes_eq(_unwrap_bytes(ref_chacha_poly_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain)).to_equal(true)
    i = i + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6efc34adf5bc78ea03154b90a1d1e5b54883d997993537581dcfb8e657284ed8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6efc34adf5bc78ea03154b90a1d1e5b54883d997993537581dcfb8e657284ed8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6efc34adf5bc78ea03154b90a1d1e5b54883d997993537581dcfb8e657284ed8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/os_crypto_random_ref_spec.spl
mirror: doc/06_spec/03_system/os/os_crypto_random_ref_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_crypto_random_ref_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_crypto_random_ref_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_crypto_random_ref_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA-256 matches Python and Node for randomized byte shapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_crypto_random_ref_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA-512 matches Python and Node for randomized byte shapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_crypto_random_ref_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HMAC-SHA256 matches Python and Node for randomized keys and messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
