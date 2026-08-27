# TLS Certificate Chain Verification Specification

> Exercises `os.tls13.cert_verify.verify_cert_chain` against static RSA-PSS

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `os.tls13.cert_verify.verify_cert_chain` against static RSA-PSS
certificate fixtures:
- valid root -> intermediate -> leaf chain
- missing trust anchor
- intermediate certificate without CA=true

tag: slow, system, tls, crypto

## Scenarios

### verify_cert_chain

#### parses leaf certificate pieces compatible with rsa_pss_sha256_verify_native

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses leaf certificate pieces compatible with rsa_pss_sha256_verify_native
   - Expected: scheme equals `0x0804`
   - Expected: spki.len() > 0 is true
   - Expected: tbs.len() > 0 is true
   - Expected: sig.len() > 0 is true
   - Expected: rsa_pss_sha256_verify_native(spki, tbs, sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses leaf certificate pieces compatible with rsa_pss_sha256_verify_native")
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
expect(rsa_pss_sha256_verify_native(spki, tbs, sig)).to_equal(true)
```

</details>

#### accepts a valid leaf -> intermediate chain anchored in the root store

- accepts a valid leaf -> intermediate chain anchored in the root store
   - Expected: observed.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts a valid leaf -> intermediate chain anchored in the root store")
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

- rejects the chain when the trust anchor is absent
   - Expected: observed.is_ok is false
   - Expected: observed.err_msg contains `"trust anchor") or observed.err_msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects the chain when the trust anchor is absent")
val intermediate = hex_to_bytes(INT_DER_HEX)
val leaf = hex_to_bytes(LEAF_DER_HEX)
val observed = observe_cert_chain(verify_cert_chain([leaf, intermediate], []))
expect(observed.is_ok).to_equal(false)
expect(observed.err_msg.contains("trust anchor") or observed.err_msg.contains("issuer")).to_equal(true)
```

</details>

#### rejects an intermediate certificate that is not marked as a CA

- rejects an intermediate certificate that is not marked as a CA
   - Expected: observed.is_ok is false
   - Expected: observed.err_msg contains `"not a CA") or observed.err_msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an intermediate certificate that is not marked as a CA")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f79a1b4c96a05d1fa37c976e6c0bc90698551f5cd3022ddeb549ee6bfbe2292d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f79a1b4c96a05d1fa37c976e6c0bc90698551f5cd3022ddeb549ee6bfbe2292d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f79a1b4c96a05d1fa37c976e6c0bc90698551f5cd3022ddeb549ee6bfbe2292d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/os_tls_cert_chain_spec.spl
mirror: doc/06_spec/03_system/os/os_tls_cert_chain_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_tls_cert_chain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_tls_cert_chain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_tls_cert_chain_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses leaf certificate pieces compatible with rsa_pss_sha256_verify_native' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_cert_chain_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a valid leaf -> intermediate chain anchored in the root store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_cert_chain_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the chain when the trust anchor is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
