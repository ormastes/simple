# Poly1305 Specification

> Tests covering Poly1305 RFC 8439 §2.5.2 — canonical test vector, Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20, Poly1305 RFC 8439 §A.3 — additional test vectors, Poly1305 edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poly1305 Specification

## Scenarios

### Poly1305 RFC 8439 §2.5.2 — canonical test vector

#### MAC of 'Cryptographic Forum Research Group' matches RFC 8439 §2.5.2

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- MAC of 'Cryptographic Forum Research Group' matches RFC 8439 §2.5.2
   - Expected: _bytes_eq(tag, _expected_tag_252()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("MAC of 'Cryptographic Forum Research Group' matches RFC 8439 §2.5.2")
val tag = poly1305_mac(_key_252(), _msg_252())
expect(_bytes_eq(tag, _expected_tag_252())).to_equal(true)
```

</details>

#### tag is exactly 16 bytes

- tag is exactly 16 bytes
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tag is exactly 16 bytes")
val tag = poly1305_mac(_key_252(), _msg_252())
expect(tag.len()).to_equal(16u64)
```

</details>

### Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20

#### poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key

- poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key
   - Expected: _bytes_eq(otk, _key_gen_expected_otk()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key")
val otk = poly1305_key_gen(_key_gen_key(), _key_gen_nonce())
expect(_bytes_eq(otk, _key_gen_expected_otk())).to_equal(true)
```

</details>

#### poly1305_key_gen always returns exactly 32 bytes

- poly1305_key_gen always returns exactly 32 bytes
   - Expected: otk.len() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("poly1305_key_gen always returns exactly 32 bytes")
val otk = poly1305_key_gen(_key_gen_key(), _key_gen_nonce())
expect(otk.len()).to_equal(32u64)
```

</details>

### Poly1305 RFC 8439 §A.3 — additional test vectors

#### Test #1: zero key + 64-byte zero message → zero tag

- Test #1: zero key + 64-byte zero message → zero tag
   - Expected: _bytes_eq(tag, _expected_tag_a3_1()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Test #1: zero key + 64-byte zero message → zero tag")
val tag = poly1305_mac(_key_a3_1(), _msg_a3_1())
expect(_bytes_eq(tag, _expected_tag_a3_1())).to_equal(true)
```

</details>

#### Test #2: r=0, s=36e5..., tag equals s regardless of message

- Test #2: r=0, s=36e5..., tag equals s regardless of message
   - Expected: _bytes_eq(tag, _expected_tag_a3_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Test #2: r=0, s=36e5..., tag equals s regardless of message")
val tag = poly1305_mac(_key_a3_2(), _msg_a3_2())
expect(_bytes_eq(tag, _expected_tag_a3_2())).to_equal(true)
```

</details>

#### Test #4: Jabberwocky 127 bytes (partial last block) → 4541669a...

- Test #4: Jabberwocky 127 bytes (partial last block) → 4541669a...
   - Expected: _bytes_eq(tag, _expected_tag_a3_4()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Test #4: Jabberwocky 127 bytes (partial last block) → 4541669a...")
val tag = poly1305_mac(_key_a3_4(), _msg_a3_4())
expect(_bytes_eq(tag, _expected_tag_a3_4())).to_equal(true)
```

</details>

### Poly1305 edge cases

#### zero-length message → tag is 16 bytes

- zero-length message → tag is 16 bytes
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zero-length message → tag is 16 bytes")
val empty: [u8] = []
val tag = poly1305_mac(_key_252(), empty)
expect(tag.len()).to_equal(16u64)
```

</details>

#### zero-length message with zero key → zero tag

- zero-length message with zero key → zero tag
   - Expected: _bytes_eq(tag, _expected_tag_a3_1()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zero-length message with zero key → zero tag")
val empty: [u8] = []
val tag = poly1305_mac(_key_a3_1(), empty)
expect(_bytes_eq(tag, _expected_tag_a3_1())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/poly1305_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Poly1305 RFC 8439 §2.5.2 — canonical test vector, Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20, Poly1305 RFC 8439 §A.3 — additional test vectors, Poly1305 edge cases.
- Poly1305 RFC 8439 §2.5.2 — canonical test vector
- Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20
- Poly1305 RFC 8439 §A.3 — additional test vectors
- Poly1305 edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `280ad479ad500638a30473e284973d99b4cf41085a3a4dbae4bf41be0859125e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `280ad479ad500638a30473e284973d99b4cf41085a3a4dbae4bf41be0859125e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `280ad479ad500638a30473e284973d99b4cf41085a3a4dbae4bf41be0859125e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/crypto/poly1305_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/poly1305_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/poly1305_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/poly1305_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/poly1305_spec.spl:275:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MAC of 'Cryptographic Forum Research Group' matches RFC 8439 §2.5.2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_spec.spl:281:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tag is exactly 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_spec.spl:289:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_spec.spl:303:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test #1: zero key + 64-byte zero message → zero tag' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/crypto/poly1305_spec.spl:309:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test #2: r=0, s=36e5..., tag equals s regardless of message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/crypto/poly1305_spec.spl:315:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test #4: Jabberwocky 127 bytes (partial last block) → 4541669a...' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
