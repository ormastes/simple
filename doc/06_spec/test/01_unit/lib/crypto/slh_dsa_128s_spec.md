# slh_dsa_128s_spec

> Exercises FIPS 205 Algorithms 6, 7, and 8 (WOTS+_genPK / sign /

<!-- sdn-diagram:id=slh_dsa_128s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=slh_dsa_128s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

slh_dsa_128s_spec -> std
slh_dsa_128s_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=slh_dsa_128s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# slh_dsa_128s_spec

Exercises FIPS 205 Algorithms 6, 7, and 8 (WOTS+_genPK / sign /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/slh_dsa_128s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## WOTS+ One-Time Signature Round-Trip

    Exercises FIPS 205 Algorithms 6, 7, and 8 (WOTS+_genPK / sign /
    pkFromSig) at the standard SLH-DSA-SHA2-128s parameter set
    (n=16, lg_w=4, len=35). Verifies that
    wots_pkFromSig(sign(m)) == wots_genPK for the same ADRS / seeds.

## Scenarios

### SLH-DSA WOTS+ — full SHA2-128s parameters

#### wots_pkFromSig(wots_sign(m)) equals wots_pk_gen at SHA2-128s params

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _filled(16u64, 0x42)
val pk = _filled(16u64, 0xA5)
val msg = _filled(16u64, 0x33)
val adrs = _wots_adrs()
val pk_direct = wots_pk_gen_128s(sk, pk, adrs)
val sig = wots_sign_128s(msg, sk, pk, adrs)
val pk_recovered = wots_pk_from_sig_128s(msg, sig, pk, adrs)
expect(pk_direct.len()).to_equal(16)
expect(sig.len()).to_equal(35 * 16)
expect(_bytes_eq(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA XMSS subtree — h_prime=2

#### xmss_pkFromSig(xmss_sign(m)) equals xmss_node root

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _filled(16u64, 0x42)
val pk = _filled(16u64, 0xA5)
val msg = _filled(16u64, 0x33)
val adrs = _xmss_adrs()
val h_prime = 2
val idx = 1
val root_direct = xmss_node(sk, 0, h_prime, pk, adrs)
val sig = xmss_sign(msg, sk, idx, h_prime, pk, adrs)
val root_recovered = xmss_pk_from_sig(idx, sig, msg, h_prime, pk, adrs)
expect(root_direct.len()).to_equal(16)
expect(sig.len()).to_equal((35 + h_prime) * 16)
expect(_bytes_eq(root_direct, root_recovered)).to_equal(true)
```

</details>

### SLH-DSA FORS — reduced (k=2, a=4)

#### fors_pkFromSig(fors_sign(md)) equals fors_pk_gen

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _filled(16u64, 0x42)
val pk = _filled(16u64, 0xA5)
# md needs k*a = 8 bits = 1 byte for (k=2, a=4).
val md = _filled(1u64, 0xC3)
val adrs = _fors_adrs()
val pk_direct = fors_pk_gen(sk, pk, adrs, 2, 4)
val sig = fors_sign(md, sk, pk, adrs, 2, 4)
val pk_recovered = fors_pk_from_sig(sig, md, pk, adrs, 2, 4)
expect(pk_direct.len()).to_equal(16)
expect(sig.len()).to_equal(2 * (1 + 4) * 16)
expect(_bytes_eq(pk_direct, pk_recovered)).to_equal(true)
```

</details>

### SLH-DSA Hypertree — reduced (d=2, h_prime=2)

#### ht_verify accepts the signature produced by ht_sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _filled(16u64, 0x42)
val pk = _filled(16u64, 0xA5)
val msg = _filled(16u64, 0x33)
val d = 2
val h_prime = 2
val pk_root = ht_pk_root(sk, pk, d, h_prime)
val idx_tree = 1
val idx_leaf = 2
val sig = ht_sign(msg, sk, pk, idx_tree, idx_leaf, d, h_prime)
expect(pk_root.len()).to_equal(16)
expect(sig.len()).to_equal(d * (35 + h_prime) * 16)
val ok = ht_verify(msg, sig, pk, idx_tree, idx_leaf, pk_root,
                    d, h_prime)
expect(ok).to_equal(true)
```

</details>

### SLH-DSA — end-to-end at reduced (d=2, h_prime=2, k=2, a=4)

#### slh_verify_internal accepts a fresh slh_sign_internal signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = _build_tamper_fixture()
val pk = fixture.0
val msg = fixture.1
val sig = fixture.2
val ok = slh_verify_internal(msg, sig, pk, 2, 2, 4, 2)
expect(pk.len()).to_equal(32)
expect(sig.len()).to_equal(1360)
expect(ok).to_equal(true)
```

</details>

#### slh_verify_internal rejects a tampered signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip bit 0 of byte 0 (the first byte of R, the message
# randomiser) — verification must reject.
val fixture = _build_tamper_fixture()
val pk = fixture.0
val msg = fixture.1
val tampered = fixture.3
val ok = slh_verify_internal(msg, tampered, pk, 2, 2, 4, 2)
expect(ok).to_equal(false)
```

</details>

### SLH-DSA-SHA2-128s — public API surface

#### exposes the FIPS 205 §11 Table 2 SHA2-128s public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference the symbols so the linker pulls them in. We do
# not invoke the full-parameter pipeline here — see the perf
# budget in the file header.
val ref_keygen = slh_dsa_128s_keygen
val ref_sign = slh_dsa_128s_sign
val ref_verify = slh_dsa_128s_verify
val pk = _filled(32u64, 0xA5)
val msg = _filled(16u64, 0x33)
val short_sig = _filled(1u64, 0x00)
expect(ref_verify(pk, msg, short_sig)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
