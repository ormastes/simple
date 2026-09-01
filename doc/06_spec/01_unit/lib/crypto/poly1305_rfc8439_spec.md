# Poly1305 Rfc8439 Specification

> Tests covering Poly1305 RFC 8439 §2.5.2 canonical test, Poly1305 RFC 8439 §A.3 additional vectors, Poly1305 tag length.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poly1305 Rfc8439 Specification

## Scenarios

### Poly1305 RFC 8439 §2.5.2 canonical test

#### MAC of 'Cryptographic Forum Research Group' → a8061dc1305136c6c22b8baf0c0127a9

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- MAC of 'Cryptographic Forum Research Group' → a8061dc1305136c6c22b8baf0c0127a9
   - Expected: poly1305_mac(KEY_252, MSG_252) equals `EXPECTED_TAG_252`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("MAC of 'Cryptographic Forum Research Group' → a8061dc1305136c6c22b8baf0c0127a9")
expect(poly1305_mac(KEY_252, MSG_252)).to_equal(EXPECTED_TAG_252)
```

</details>

### Poly1305 RFC 8439 §A.3 additional vectors

#### Test #1: zero key + 64-byte zero message → 16-byte zero tag

- Test #1: zero key + 64-byte zero message → 16-byte zero tag
   - Expected: poly1305_mac(KEY_ZERO, MSG_ZERO) equals `TAG_ZERO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Test #1: zero key + 64-byte zero message → 16-byte zero tag")
expect(poly1305_mac(KEY_ZERO, MSG_ZERO)).to_equal(TAG_ZERO)
```

</details>

#### Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62

- Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62
   - Expected: poly1305_mac(KEY_TEST4, MSG_TEST4) equals `EXPECTED_TAG_TEST4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62")
expect(poly1305_mac(KEY_TEST4, MSG_TEST4)).to_equal(EXPECTED_TAG_TEST4)
```

</details>

### Poly1305 tag length

#### poly1305_mac always returns exactly 16 bytes

- poly1305_mac always returns exactly 16 bytes
   - Expected: poly1305_mac(KEY_252, MSG_252).len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poly1305_mac always returns exactly 16 bytes")
expect(poly1305_mac(KEY_252, MSG_252).len()).to_equal(16)
```

</details>

#### poly1305_mac on zero key returns exactly 16 bytes

- poly1305_mac on zero key returns exactly 16 bytes
   - Expected: poly1305_mac(KEY_ZERO, MSG_ZERO).len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poly1305_mac on zero key returns exactly 16 bytes")
expect(poly1305_mac(KEY_ZERO, MSG_ZERO).len()).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Poly1305 RFC 8439 §2.5.2 canonical test, Poly1305 RFC 8439 §A.3 additional vectors, Poly1305 tag length.
- Poly1305 RFC 8439 §2.5.2 canonical test
- Poly1305 RFC 8439 §A.3 additional vectors
- Poly1305 tag length

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25028615b58d1302074c823dbf718ddb89276f1d10e792139ff07671ab961b2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25028615b58d1302074c823dbf718ddb89276f1d10e792139ff07671ab961b2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25028615b58d1302074c823dbf718ddb89276f1d10e792139ff07671ab961b2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/poly1305_rfc8439_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/poly1305_rfc8439_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/poly1305_rfc8439_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MAC of 'Cryptographic Forum Research Group' → a8061dc1305136c6c22b8baf0c0127a9' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test #1: zero key + 64-byte zero message → 16-byte zero tag' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Test #1: zero key + 64-byte zero message → 16-byte zero tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:145:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
