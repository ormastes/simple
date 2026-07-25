# TLS Certificate Chain Verification Specification

> Exercises `os.tls13.cert_verify.verify_cert_chain` against static RSA-PSS

<!-- sdn-diagram:id=os_tls_cert_chain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_cert_chain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_cert_chain_spec -> std
os_tls_cert_chain_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_cert_chain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TLS Certificate Chain Verification Specification

Exercises `os.tls13.cert_verify.verify_cert_chain` against static RSA-PSS

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_cert_chain_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `os.tls13.cert_verify.verify_cert_chain` against static RSA-PSS
certificate fixtures:
- valid root -> intermediate -> leaf chain
- missing trust anchor
- intermediate certificate without CA=true

tag: slow, system, tls, crypto

## Scenarios

### verify_cert_chain

#### parses leaf certificate pieces compatible with rsa_pss_sha256_verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intermediate = hex_to_bytes(INT_DER_HEX)
val leaf = hex_to_bytes(LEAF_DER_HEX)
val scheme = extract_certificate_signature_scheme(leaf)
expect(scheme).to_equal(0x0804)
val spki = extract_rsa_pubkey_spki_from_cert(intermediate)
val tbs = extract_tbs_certificate_bytes(leaf)
val sig = extract_certificate_signature_bytes(leaf)
expect(spki.len() > 0).to_equal(true)
expect(tbs.len() > 0).to_equal(true)
expect(sig.len() > 0).to_equal(true)
expect(rsa_pss_sha256_verify(spki, tbs, sig)).to_equal(true)
```

</details>

#### accepts a valid leaf -> intermediate chain anchored in the root store

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = hex_to_bytes(ROOT_DER_HEX)
val intermediate = hex_to_bytes(INT_DER_HEX)
val leaf = hex_to_bytes(LEAF_DER_HEX)
val observed = observe_cert_chain(verify_cert_chain([leaf, intermediate], [root]))
if not observed.is_ok:
    print "unexpected verify_cert_chain failure: {observed.err_msg}"
expect(observed.is_ok).to_equal(true)
```

</details>

#### rejects the chain when the trust anchor is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intermediate = hex_to_bytes(INT_DER_HEX)
val leaf = hex_to_bytes(LEAF_DER_HEX)
val observed = observe_cert_chain(verify_cert_chain([leaf, intermediate], []))
expect(observed.is_ok).to_equal(false)
expect(observed.err_msg.contains("trust anchor") or observed.err_msg.contains("issuer")).to_equal(true)
```

</details>

#### rejects an intermediate certificate that is not marked as a CA

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = hex_to_bytes(ROOT_DER_HEX)
val bad_intermediate = hex_to_bytes(BAD_INT_DER_HEX)
val leaf = hex_to_bytes(LEAF_DER_HEX)
val observed = observe_cert_chain(verify_cert_chain([leaf, bad_intermediate], [root]))
expect(observed.is_ok).to_equal(false)
expect(observed.err_msg.contains("not a CA") or observed.err_msg.contains("mismatch")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
