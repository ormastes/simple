# Hmac Sha1 Specification

> Tests covering HMAC-SHA-1 — RFC 2202 §3 reference vectors, HMAC-SHA-1 — output shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Sha1 Specification

## Scenarios

### HMAC-SHA-1 — RFC 2202 §3 reference vectors

#### TC1: K=20*0x0b, M='Hi There'

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC1: K=20*0x0b, M='Hi There'


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: K=20*0x0b, M='Hi There'")
# MAC = b617318655057264e28bc0b6fb378c8ef146be00
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0x0b, 20), [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65]))).to_equal(
    "b617318655057264e28bc0b6fb378c8ef146be00"
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
# MAC = effcdf6ae5eb2fa2d27416d5f184df9c259a7c79
expect(bytes_to_hex(hmac_sha1("Jefe", "what do ya want for nothing?"))).to_equal(
    "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"
)
```

</details>

#### TC3: K=20*0xaa, M=50*0xdd

- TC3: K=20*0xaa, M=50*0xdd


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC3: K=20*0xaa, M=50*0xdd")
# MAC = 125d7342b9ac11cd91a39af48aa17b4f63f175d3
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0xaa, 20), _bytes_repeat(0xdd, 50)))).to_equal(
    "125d7342b9ac11cd91a39af48aa17b4f63f175d3"
)
```

</details>

#### TC4: K=25-byte 0x01..0x19, M=50*0xcd

- TC4: K=25-byte 0x01..0x19, M=50*0xcd


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC4: K=25-byte 0x01..0x19, M=50*0xcd")
# MAC = 4c9007f4026250c6bc8414f9bf50c86c2d7235da
expect(bytes_to_hex(hmac_sha1_bytes(_tc4_key(), _bytes_repeat(0xcd, 50)))).to_equal(
    "4c9007f4026250c6bc8414f9bf50c86c2d7235da"
)
```

</details>

#### TC6: K=80*0xaa (longer than block), short data — exercises inner-hash key path

- TC6: K=80*0xaa (longer than block), short data — exercises inner-hash key path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC6: K=80*0xaa (longer than block), short data — exercises inner-hash key path")
# 'Test Using Larger Than Block-Size Key - Hash Key First'
# MAC = aa4ae5e15272d00e95705637ce8a3b55ed402112
val msg = [
    0x54, 0x65, 0x73, 0x74, 0x20, 0x55, 0x73, 0x69, 0x6e, 0x67, 0x20, 0x4c, 0x61, 0x72, 0x67, 0x65,
    0x72, 0x20, 0x54, 0x68, 0x61, 0x6e, 0x20, 0x42, 0x6c, 0x6f, 0x63, 0x6b, 0x2d, 0x53, 0x69, 0x7a,
    0x65, 0x20, 0x4b, 0x65, 0x79, 0x20, 0x2d, 0x20, 0x48, 0x61, 0x73, 0x68, 0x20, 0x4b, 0x65, 0x79,
    0x20, 0x46, 0x69, 0x72, 0x73, 0x74
]
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0xaa, 80), msg))).to_equal(
    "aa4ae5e15272d00e95705637ce8a3b55ed402112"
)
```

</details>

### HMAC-SHA-1 — output shape

#### MAC is exactly 20 bytes

- MAC is exactly 20 bytes
   - Expected: hmac_sha1("k", "m").len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAC is exactly 20 bytes")
expect(hmac_sha1("k", "m").len()).to_equal(20)
```

</details>

#### hex form is exactly 40 chars

- hex form is exactly 40 chars
   - Expected: bytes_to_hex(hmac_sha1("k", "m")).len() equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex form is exactly 40 chars")
expect(bytes_to_hex(hmac_sha1("k", "m")).len()).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/crypto/hmac_sha1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HMAC-SHA-1 — RFC 2202 §3 reference vectors, HMAC-SHA-1 — output shape.
- HMAC-SHA-1 — RFC 2202 §3 reference vectors
- HMAC-SHA-1 — output shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `b850569086c4f83943c50d435db29eacc8144fc8e69a8382728d10e664e4168f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b850569086c4f83943c50d435db29eacc8144fc8e69a8382728d10e664e4168f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b850569086c4f83943c50d435db29eacc8144fc8e69a8382728d10e664e4168f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/crypto/hmac_sha1_spec.spl
mirror: doc/06_spec/unit/lib/common/crypto/hmac_sha1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/crypto/hmac_sha1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/crypto/hmac_sha1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/crypto/hmac_sha1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/crypto/hmac_sha1_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1: K=20*0x0b, M='Hi There'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/hmac_sha1_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC2: K='Jefe', M='what do ya want for nothing?'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/hmac_sha1_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC3: K=20*0xaa, M=50*0xdd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
