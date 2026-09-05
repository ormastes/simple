# Rsa Contract Parity Specification

> Tests covering RSA signing contract backend selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Contract Parity Specification

## Scenarios

### RSA signing contract backend selection

#### Auto matches HostedReference for a valid SHA-512 RSA fixture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Auto matches HostedReference for a valid SHA-512 RSA fixture
   - Expected: auto_sig equals `hosted_sig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Auto matches HostedReference for a valid SHA-512 RSA fixture")
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val msg = _test_message()
val auto_sig = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.Auto)
val hosted_sig = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
expect(auto_sig.len()).to_be_greater_than(0)
expect(auto_sig).to_equal(hosted_sig)
```

</details>

#### HostedReference SHA-512 signing is deterministic

- HostedReference SHA-512 signing is deterministic
   - Expected: sig_a equals `sig_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HostedReference SHA-512 signing is deterministic")
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val msg = _test_message()
val sig_a = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
val sig_b = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
expect(sig_a.len()).to_be_greater_than(0)
expect(sig_a).to_equal(sig_b)
```

</details>

#### PureSimple SHA-512 signing is deterministic

- PureSimple SHA-512 signing is deterministic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PureSimple SHA-512 signing is deterministic")
# Pure-Simple RSA modexp on a 2048-bit key exceeds the interpreter
# wall-clock budget.  Skip until compiled-mode test runner lands.
return "skip: pure-Simple 2048-bit modexp too slow for interpreter"
```

</details>

#### PureSimple SHA-512 matches HostedReference byte-for-byte and verifies

- PureSimple SHA-512 matches HostedReference byte-for-byte and verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PureSimple SHA-512 matches HostedReference byte-for-byte and verifies")
# Pure-Simple RSA modexp on a 2048-bit key exceeds the interpreter
# wall-clock budget.  Skip until compiled-mode test runner lands.
return "skip: pure-Simple 2048-bit modexp too slow for interpreter"
```

</details>

#### malformed PKCS#8 returns empty signatures for SHA-256 and SHA-512 across backends

- malformed PKCS#8 returns empty signatures for SHA-256 and SHA-512 across backends
   - Expected: rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference) equals `[]`
   - Expected: rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple) equals `[]`
   - Expected: rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference) equals `[]`
   - Expected: rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("malformed PKCS#8 returns empty signatures for SHA-256 and SHA-512 across backends")
val malformed = _malformed_pkcs8()
val msg = _test_message()
expect(rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple)).to_equal([])
expect(rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple)).to_equal([])
```

</details>

#### wrong key type returns empty SHA-512 signatures across backends

- wrong key type returns empty SHA-512 signatures across backends
   - Expected: rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.HostedReference) equals `[]`
   - Expected: rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.PureSimple) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong key type returns empty SHA-512 signatures across backends")
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val ec_pkcs8 = _load_bytes(EC_PK8)
val msg = _test_message()
expect(rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.PureSimple)).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/rsa_contract_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RSA signing contract backend selection.
- RSA signing contract backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d5ce525edb4fa960211db6a1e8c9810049fda448ba6ad4d52c078e1bf71b852a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5ce525edb4fa960211db6a1e8c9810049fda448ba6ad4d52c078e1bf71b852a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5ce525edb4fa960211db6a1e8c9810049fda448ba6ad4d52c078e1bf71b852a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/rsa_contract_parity_spec.spl
mirror: doc/06_spec/unit/os/crypto/rsa_contract_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/rsa_contract_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/rsa_contract_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/rsa_contract_parity_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Auto matches HostedReference for a valid SHA-512 RSA fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/rsa_contract_parity_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HostedReference SHA-512 signing is deterministic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/rsa_contract_parity_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PureSimple SHA-512 signing is deterministic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
