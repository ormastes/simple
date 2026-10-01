# Hmac Sha3 Specification

> Tests covering HMAC-SHA3-256 — published reference vectors, HMAC-SHA3-384 — published reference vectors, HMAC-SHA3-512 — published reference vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Sha3 Specification

## Scenarios

### HMAC-SHA3-256 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)")
# MAC = ba85192310dffa96e2a3a40e69774351140bb7185e1202cdcc917589f95e16bb
expect(bytes_to_hex(hmac_sha3_256_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "ba85192310dffa96e2a3a40e69774351140bb7185e1202cdcc917589f95e16bb"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

- TC2: K='Jefe', M='what do ya want for nothing?'


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: K='Jefe', M='what do ya want for nothing?'")
# MAC = c7d4072e788877ae3596bbb0da73b887c9171f93095b294ae857fbe2645e1ba5
expect(bytes_to_hex(hmac_sha3_256("Jefe", "what do ya want for nothing?"))).to_equal(
    "c7d4072e788877ae3596bbb0da73b887c9171f93095b294ae857fbe2645e1ba5"
)
```

</details>

### HMAC-SHA3-384 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

- TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)")
# MAC = 68d2dcf7fd4ddd0a2240c8a437305f61fb7334cfb5d0226e1bc27dc1
#       0a2e723a20d370b47743130e26ac7e3d532886bd
expect(bytes_to_hex(hmac_sha3_384_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "68d2dcf7fd4ddd0a2240c8a437305f61fb7334cfb5d0226e1bc27dc10a2e723a20d370b47743130e26ac7e3d532886bd"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

- TC2: K='Jefe', M='what do ya want for nothing?'


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: K='Jefe', M='what do ya want for nothing?'")
# MAC = f1101f8cbf9766fd6764d2ed61903f21ca9b18f57cf3e1a23ca13508a93243ce
#       48c045dc007f26a21b3f5e0e9df4c20a
expect(bytes_to_hex(hmac_sha3_384("Jefe", "what do ya want for nothing?"))).to_equal(
    "f1101f8cbf9766fd6764d2ed61903f21ca9b18f57cf3e1a23ca13508a93243ce48c045dc007f26a21b3f5e0e9df4c20a"
)
```

</details>

### HMAC-SHA3-512 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

- TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)")
# MAC = eb3fbd4b2eaab8f5c504bd3a41465aacec15770a7cabac531e482f86
#       0b5ec7ba47ccb2c6f2afce8f88d22b6dc61380f23
#       a668fd3888bb80537c0a0b86407689e
expect(bytes_to_hex(hmac_sha3_512_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "eb3fbd4b2eaab8f5c504bd3a41465aacec15770a7cabac531e482f860b5ec7ba47ccb2c6f2afce8f88d22b6dc61380f23a668fd3888bb80537c0a0b86407689e"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

- TC2: K='Jefe', M='what do ya want for nothing?'


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: K='Jefe', M='what do ya want for nothing?'")
# MAC = 5a4bfeab6166427c7a3647b747292b8384537cdb89afb3bf5665e4c5e
#       709350b287baec921fd7ca0ee7a0c31d022a95e1
#       fc92ba9d77df883960275beb4e62024
expect(bytes_to_hex(hmac_sha3_512("Jefe", "what do ya want for nothing?"))).to_equal(
    "5a4bfeab6166427c7a3647b747292b8384537cdb89afb3bf5665e4c5e709350b287baec921fd7ca0ee7a0c31d022a95e1fc92ba9d77df883960275beb4e62024"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hmac_sha3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HMAC-SHA3-256 — published reference vectors, HMAC-SHA3-384 — published reference vectors, HMAC-SHA3-512 — published reference vectors.
- HMAC-SHA3-256 — published reference vectors
- HMAC-SHA3-384 — published reference vectors
- HMAC-SHA3-512 — published reference vectors

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

- Canonical SPipe generation for source `059edbbf68e4ea77b2cd8b4f927158fbcd4f41df8ee910ca0824677c4814b9c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `059edbbf68e4ea77b2cd8b4f927158fbcd4f41df8ee910ca0824677c4814b9c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `059edbbf68e4ea77b2cd8b4f927158fbcd4f41df8ee910ca0824677c4814b9c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/crypto/hmac_sha3_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/hmac_sha3_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/hmac_sha3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/hmac_sha3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/hmac_sha3_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/hmac_sha3_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC2: K='Jefe', M='what do ya want for nothing?'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/hmac_sha3_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
