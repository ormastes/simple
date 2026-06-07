# slh_dsa_192s_256s_spec

> Exercises the _p variants of wots_pk_gen / sign / pkFromSig with

<!-- sdn-diagram:id=slh_dsa_192s_256s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=slh_dsa_192s_256s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

slh_dsa_192s_256s_spec -> std
slh_dsa_192s_256s_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=slh_dsa_192s_256s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# slh_dsa_192s_256s_spec

Exercises the _p variants of wots_pk_gen / sign / pkFromSig with

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/slh_dsa_192s_256s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## WOTS+ Round-Trip — SHA2-192s

    Exercises the _p variants of wots_pk_gen / sign / pkFromSig with
    n=24 and hash_id=SHA-512. Verifies that wots_pkFromSig(sign(m))
    equals wots_pk_gen for the same ADRS and seeds.

## Scenarios

### SLH-DSA-SHA2-192s WOTS+ — n=24 SHA-512 parameters

#### wots_pkFromSig(wots_sign(m)) equals wots_pk_gen at SHA2-192s params

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val adrs = _wots_adrs_p()
val pk_direct = wots_pk_gen_p(sk, pk, adrs, n, hash_id)
val sig = wots_sign_p(msg, sk, pk, adrs, n, hash_id)
val pk_recovered = wots_pk_from_sig_p(msg, sig, pk, adrs, n, hash_id)
expect(pk_direct.len()).to_equal(24)
expect(sig.len()).to_equal(_slh_wots_len(n).to_u64() * n)
expect(_bytes_eq_p(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-192s XMSS subtree — h_prime=2 n=24

#### xmss_pkFromSig(xmss_sign(m)) equals xmss_node root at n=24 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val adrs = _xmss_adrs_p()
val h_prime = 2
val idx = 1
val root_direct = xmss_node_p(sk, 0, h_prime, pk, adrs, n, hash_id)
val sig = xmss_sign_p(msg, sk, idx, h_prime, pk, adrs, n, hash_id)
val root_recovered = xmss_pk_from_sig_p(idx, sig, msg, h_prime, pk, adrs, n, hash_id)
expect(root_direct.len()).to_equal(24)
expect(sig.len()).to_equal(xmss_sig_len_p(h_prime, n))
expect(_bytes_eq_p(root_direct, root_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-192s FORS — reduced (k=4, a=2) n=24

#### fors_pkFromSig(fors_sign(md)) equals fors_pk_gen at n=24 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
# md needs k*a = 4*2 = 8 bits = 1 byte for (k=4, a=2).
val md = _filled_p(1u64, 0xC3)
val adrs = _fors_adrs_p()
val pk_direct = fors_pk_gen_p(sk, pk, adrs, 4, 2, n, hash_id)
val sig = fors_sign_p(md, sk, pk, adrs, 4, 2, n, hash_id)
val pk_recovered = fors_pk_from_sig_p(sig, md, pk, adrs, 4, 2, n, hash_id)
expect(pk_direct.len()).to_equal(24)
expect(sig.len()).to_equal(fors_sig_len_p(4, 2, n))
expect(_bytes_eq_p(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-192s Hypertree — reduced (d=2, h_prime=2) n=24

#### ht_verify accepts ht_sign signature at n=24 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val d = 2
val h_prime = 2
val pk_root = ht_pk_root_p(sk, pk, d, h_prime, n, hash_id)
val idx_tree = 1
val idx_leaf = 2
val sig = ht_sign_p(msg, sk, pk, idx_tree, idx_leaf, d, h_prime, n, hash_id)
expect(pk_root.len()).to_equal(24)
expect(sig.len()).to_equal(ht_sig_len_p(d, h_prime, n))
val ok = ht_verify_p(msg, sig, pk, idx_tree, idx_leaf, pk_root, d, h_prime, n, hash_id)
expect(ok).to_equal(true)
```

</details>

### SLH-DSA-SHA2-192s — end-to-end at reduced (d=2, h'=2, k=4, a=2)

#### slh_verify_internal_p accepts a fresh slh_sign_internal_p signature (192s)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = _build_tamper_fixture_192s()
val pk = fixture.0
val msg = fixture.1
val sig = fixture.2
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val ok = slh_verify_internal_p(msg, sig, pk, 2, 2, 2, 4, n, 3, hash_id)
expect(pk.len()).to_equal(48)
expect(sig.len()).to_equal(2856)
expect(ok).to_equal(true)
```

</details>

#### slh_verify_internal_p rejects a tampered signature (192s)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = _build_tamper_fixture_192s()
val pk = fixture.0
val msg = fixture.1
val tampered = fixture.3
val n: u64 = 24u64
val hash_id = _slh_hash_sha512()
val ok = slh_verify_internal_p(msg, tampered, pk, 2, 2, 2, 4, n, 3, hash_id)
expect(ok).to_equal(false)
```

</details>

### SLH-DSA-SHA2-256s WOTS+ — n=32 SHA-512 parameters

#### wots_pkFromSig(wots_sign(m)) equals wots_pk_gen at SHA2-256s params

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val adrs = _wots_adrs_p()
val pk_direct = wots_pk_gen_p(sk, pk, adrs, n, hash_id)
val sig = wots_sign_p(msg, sk, pk, adrs, n, hash_id)
val pk_recovered = wots_pk_from_sig_p(msg, sig, pk, adrs, n, hash_id)
expect(pk_direct.len()).to_equal(32)
expect(sig.len()).to_equal(_slh_wots_len(n).to_u64() * n)
expect(_bytes_eq_p(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-256s XMSS subtree — h_prime=2 n=32

#### xmss_pkFromSig(xmss_sign(m)) equals xmss_node root at n=32 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val adrs = _xmss_adrs_p()
val h_prime = 2
val idx = 1
val root_direct = xmss_node_p(sk, 0, h_prime, pk, adrs, n, hash_id)
val sig = xmss_sign_p(msg, sk, idx, h_prime, pk, adrs, n, hash_id)
val root_recovered = xmss_pk_from_sig_p(idx, sig, msg, h_prime, pk, adrs, n, hash_id)
expect(root_direct.len()).to_equal(32)
expect(sig.len()).to_equal(xmss_sig_len_p(h_prime, n))
expect(_bytes_eq_p(root_direct, root_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-256s FORS — reduced (k=4, a=2) n=32

#### fors_pkFromSig(fors_sign(md)) equals fors_pk_gen at n=32 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
# md needs k*a = 4*2 = 8 bits = 1 byte for (k=4, a=2).
val md = _filled_p(1u64, 0xC3)
val adrs = _fors_adrs_p()
val pk_direct = fors_pk_gen_p(sk, pk, adrs, 4, 2, n, hash_id)
val sig = fors_sign_p(md, sk, pk, adrs, 4, 2, n, hash_id)
val pk_recovered = fors_pk_from_sig_p(sig, md, pk, adrs, 4, 2, n, hash_id)
expect(pk_direct.len()).to_equal(32)
expect(sig.len()).to_equal(fors_sig_len_p(4, 2, n))
expect(_bytes_eq_p(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA-SHA2-256s Hypertree — reduced (d=2, h_prime=2) n=32

#### ht_verify accepts ht_sign signature at n=32 SHA-512

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val sk = _filled_p(n, 0x42)
val pk = _filled_p(n, 0xA5)
val msg = _filled_p(n, 0x33)
val d = 2
val h_prime = 2
val pk_root = ht_pk_root_p(sk, pk, d, h_prime, n, hash_id)
val idx_tree = 1
val idx_leaf = 2
val sig = ht_sign_p(msg, sk, pk, idx_tree, idx_leaf, d, h_prime, n, hash_id)
expect(pk_root.len()).to_equal(32)
expect(sig.len()).to_equal(ht_sig_len_p(d, h_prime, n))
val ok = ht_verify_p(msg, sig, pk, idx_tree, idx_leaf, pk_root, d, h_prime, n, hash_id)
expect(ok).to_equal(true)
```

</details>

### SLH-DSA-SHA2-256s — end-to-end at reduced (d=2, h'=2, k=4, a=2)

#### slh_verify_internal_p accepts a fresh slh_sign_internal_p signature (256s)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = _build_tamper_fixture_256s()
val pk = fixture.0
val msg = fixture.1
val sig = fixture.2
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val ok = slh_verify_internal_p(msg, sig, pk, 2, 2, 2, 4, n, 3, hash_id)
expect(pk.len()).to_equal(64)
expect(sig.len()).to_equal(4832)
expect(ok).to_equal(true)
```

</details>

#### slh_verify_internal_p rejects a tampered signature (256s)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = _build_tamper_fixture_256s()
val pk = fixture.0
val msg = fixture.1
val tampered = fixture.3
val n: u64 = 32u64
val hash_id = _slh_hash_sha512()
val ok = slh_verify_internal_p(msg, tampered, pk, 2, 2, 2, 4, n, 3, hash_id)
expect(ok).to_equal(false)
```

</details>

### SLH-DSA-SHA2-192s/256s — public API surface

#### exposes the FIPS 205 §11 Table 2 SHA2-192s public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref_keygen = slh_dsa_192s_keygen
val ref_sign = slh_dsa_192s_sign
val ref_verify = slh_dsa_192s_verify
val pk = _filled_p(48u64, 0xA5)
val msg = _filled_p(24u64, 0x33)
val short_sig = _filled_p(1u64, 0x00)
expect(ref_verify(pk, msg, short_sig)).to_equal(false)
```

</details>

#### exposes the FIPS 205 §11 Table 2 SHA2-256s public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref_keygen = slh_dsa_256s_keygen
val ref_sign = slh_dsa_256s_sign
val ref_verify = slh_dsa_256s_verify
val pk = _filled_p(64u64, 0xA5)
val msg = _filled_p(32u64, 0x33)
val short_sig = _filled_p(1u64, 0x00)
expect(ref_verify(pk, msg, short_sig)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
