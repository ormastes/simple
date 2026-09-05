# OS Crypto Random Reference Comparison

> Small deterministic randomized comparison tests for the hosted security

<!-- sdn-diagram:id=os_crypto_random_ref_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_crypto_random_ref_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_crypto_random_ref_spec -> std
os_crypto_random_ref_spec -> os
os_crypto_random_ref_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_crypto_random_ref_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Small deterministic randomized comparison tests for the hosted security
primitive surface. Inputs are generated in-process, then Simple outputs are
compared with the existing Python and Node reference modules.

## Scenarios

### os_crypto_random_ref: hash and MAC random input comparison

#### SHA-256 matches Python and Node for randomized byte shapes

1.  seed
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  seed
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  seed
   - Expected: simple equals `py`
   - Expected: simple equals `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  seed
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(py)`
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(node)`
   - Expected: _aes128_decrypt_ok(key, nonce, aad, py, plain) is true
   - Expected: _bytes_eq(_unwrap_bytes(ref_aes_128_gcm_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  seed
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(py)`
   - Expected: bytes_to_hex(simple) equals `bytes_to_hex(node)`
   - Expected: _chacha_decrypt_ok(key, nonce, aad, py, plain) is true
   - Expected: _bytes_eq(_unwrap_bytes(ref_chacha_poly_decrypt_via(Vendor.PYTHON, key, nonce, aad, simple)), plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
