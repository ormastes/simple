# Rc4 Specification

> Tests covering RC4 — known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rc4 Specification

## Scenarios

### RC4 — known-answer vectors

#### Key='Key', pt='Plaintext' -> BBF316E8D940AF0AD3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Key='Key', pt='Plaintext' -> BBF316E8D940AF0AD3
   - Expected: _bytes_hex(ct) equals `BBF316E8D940AF0AD3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Key='Key', pt='Plaintext' -> BBF316E8D940AF0AD3")
var ct = rc4_encrypt(_key_key(), _pt_plaintext())
expect(_bytes_hex(ct)).to_equal("BBF316E8D940AF0AD3")
```

</details>

#### Key='Wiki', pt='pedia' -> 1021BF0420

- Key='Wiki', pt='pedia' -> 1021BF0420
   - Expected: _bytes_hex(ct) equals `1021BF0420`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Key='Wiki', pt='pedia' -> 1021BF0420")
var ct = rc4_encrypt(_key_wiki(), _pt_pedia())
expect(_bytes_hex(ct)).to_equal("1021BF0420")
```

</details>

#### Key='Secret', pt='Attack at dawn' -> 45A01F645FC35B383552544B9BF5

- Key='Secret', pt='Attack at dawn' -> 45A01F645FC35B383552544B9BF5
   - Expected: _bytes_hex(ct) equals `45A01F645FC35B383552544B9BF5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Key='Secret', pt='Attack at dawn' -> 45A01F645FC35B383552544B9BF5")
var ct = rc4_encrypt(_key_secret(), _pt_attack_at_dawn())
expect(_bytes_hex(ct)).to_equal("45A01F645FC35B383552544B9BF5")
```

</details>

#### rc4_decrypt is self-inverse of rc4_encrypt

- rc4_decrypt is self-inverse of rc4_encrypt
   - Expected: _bytes_hex(pt) equals `_bytes_hex(_pt_attack_at_dawn())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc4_decrypt is self-inverse of rc4_encrypt")
var ct = rc4_encrypt(_key_secret(), _pt_attack_at_dawn())
var pt = rc4_decrypt(_key_secret(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_pt_attack_at_dawn()))
```

</details>

#### RFC 6229: Key=0x0102030405, keystream[0:16] -> B2396305F03DC027CCC3524A0A1118A8

- RFC 6229: Key=0x0102030405, keystream[0:16] -> B2396305F03DC027CCC3524A0A1118A8
   - Expected: _bytes_hex(ks) equals `B2396305F03DC027CCC3524A0A1118A8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RFC 6229: Key=0x0102030405, keystream[0:16] -> B2396305F03DC027CCC3524A0A1118A8")
var ks = rc4_keystream(_key_rfc6229_5byte(), 16)
expect(_bytes_hex(ks)).to_equal("B2396305F03DC027CCC3524A0A1118A8")
```

</details>

#### rc4_encrypt output length equals input length

- rc4_encrypt output length equals input length
   - Expected: ct.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc4_encrypt output length equals input length")
var ct = rc4_encrypt(_key_key(), _pt_plaintext())
expect(ct.len()).to_equal(9)
```

</details>

#### rc4_init returns 256-element S-box

- rc4_init returns 256-element S-box
   - Expected: state.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc4_init returns 256-element S-box")
var state = rc4_init(_key_key())
expect(state.len()).to_equal(256)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/rc4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RC4 — known-answer vectors.
- RC4 — known-answer vectors

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

- Canonical SPipe generation for source `fbc216d82091beda2a1379e57d2f22acf990c00f833150c3bc848d1993b30e6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbc216d82091beda2a1379e57d2f22acf990c00f833150c3bc848d1993b30e6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbc216d82091beda2a1379e57d2f22acf990c00f833150c3bc848d1993b30e6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/rc4_spec.spl
mirror: doc/06_spec/unit/os/crypto/rc4_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/rc4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/rc4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/rc4_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/rc4_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Key='Key', pt='Plaintext' -> BBF316E8D940AF0AD3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/rc4_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Key='Wiki', pt='pedia' -> 1021BF0420' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/rc4_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Key='Secret', pt='Attack at dawn' -> 45A01F645FC35B383552544B9BF5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
