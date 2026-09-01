# Sha512 Verify Specification

> Tests covering SHA-512 NIST vectors, SHA-384 NIST vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha512 Verify Specification

## Scenarios

### SHA-512 NIST vectors

#### sha512('') = cf83e135...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sha512('') = cf83e135...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha512('') = cf83e135...")
expect(bytes_to_hex(sha512_bytes([]))).to_equal(
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
)
```

</details>

#### sha512('abc') = ddaf35a1...

- sha512('abc') = ddaf35a1...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha512('abc') = ddaf35a1...")
expect(bytes_to_hex(sha512_bytes(text_to_bytes("abc")))).to_equal(
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
)
```

</details>

### SHA-384 NIST vectors

#### sha384('') = 38b060a7...

- sha384('') = 38b060a7...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha384('') = 38b060a7...")
expect(bytes_to_hex(sha384_bytes([]))).to_equal(
    "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
)
```

</details>

#### sha384('abc') = cb00753f...

- sha384('abc') = cb00753f...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha384('abc') = cb00753f...")
expect(bytes_to_hex(sha384_bytes(text_to_bytes("abc")))).to_equal(
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/crypto/sha512_verify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-512 NIST vectors, SHA-384 NIST vectors.
- SHA-512 NIST vectors
- SHA-384 NIST vectors

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aaa2f9b112cc504a61f4258de9b5276079726e2dcc4931c867b541e534f45288`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aaa2f9b112cc504a61f4258de9b5276079726e2dcc4931c867b541e534f45288`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aaa2f9b112cc504a61f4258de9b5276079726e2dcc4931c867b541e534f45288`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/crypto/sha512_verify_spec.spl
mirror: doc/06_spec/unit/lib/common/crypto/sha512_verify_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/crypto/sha512_verify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/crypto/sha512_verify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/crypto/sha512_verify_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sha512('') = cf83e135...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha512_verify_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sha512('abc') = ddaf35a1...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha512_verify_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sha384('') = 38b060a7...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
