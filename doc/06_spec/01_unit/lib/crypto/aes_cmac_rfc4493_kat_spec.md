# Aes Cmac Rfc4493 Kat Specification

> Tests covering AES-128-CMAC RFC 4493 §2.3 subkey generation, AES-128-CMAC RFC 4493 §4 generation vectors, AES-128-CMAC RFC 4493 §2.5 verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Cmac Rfc4493 Kat Specification

## Scenarios

### AES-128-CMAC RFC 4493 §2.3 subkey generation

#### K1 matches RFC 4493 §4 reference (fbeed618…)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- K1 matches RFC 4493 §4 reference (fbeed618…)
   - Expected: k1 equals `_expected_K1()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("K1 matches RFC 4493 §4 reference (fbeed618…)")
val (k1, _) = aes128_cmac_subkeys(_rfc4493_key())
expect(k1).to_equal(_expected_K1())
```

</details>

#### K2 matches RFC 4493 §4 reference (f7ddac30…)

- K2 matches RFC 4493 §4 reference (f7ddac30…)
   - Expected: k2 equals `_expected_K2()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("K2 matches RFC 4493 §4 reference (f7ddac30…)")
val (_, k2) = aes128_cmac_subkeys(_rfc4493_key())
expect(k2).to_equal(_expected_K2())
```

</details>

### AES-128-CMAC RFC 4493 §4 generation vectors

#### Example 1: Mlen=0 → bb1d6929 e9593728 7fa37d12 9b756746

- Example 1: Mlen=0 → bb1d6929 e9593728 7fa37d12 9b756746
   - Expected: aes128_cmac_compute(_rfc4493_key(), _msg_empty()) equals `_tag_empty()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Example 1: Mlen=0 → bb1d6929 e9593728 7fa37d12 9b756746")
# Empty message exercises the K2 (partial-block) path.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_empty())).to_equal(_tag_empty())
```

</details>

#### Example 2: Mlen=16 → 070a16b4 6b4d4144 f79bdd9d d04a287c

- Example 2: Mlen=16 → 070a16b4 6b4d4144 f79bdd9d d04a287c
   - Expected: aes128_cmac_compute(_rfc4493_key(), _msg_16()) equals `_tag_16()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Example 2: Mlen=16 → 070a16b4 6b4d4144 f79bdd9d d04a287c")
# Single full block exercises the K1 (full-block) path.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_16())).to_equal(_tag_16())
```

</details>

#### Example 3: Mlen=40 → dfa66747 de9ae630 30ca3261 1497c827

- Example 3: Mlen=40 → dfa66747 de9ae630 30ca3261 1497c827
   - Expected: aes128_cmac_compute(_rfc4493_key(), _msg_40()) equals `_tag_40()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Example 3: Mlen=40 → dfa66747 de9ae630 30ca3261 1497c827")
# 40 = 2 full blocks + 8-byte partial; exercises the K2 path with
# a non-empty partial last block.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_40())).to_equal(_tag_40())
```

</details>

#### Example 4: Mlen=64 → 51f0bebf 7e3b9d92 fc497417 79363cfe

- Example 4: Mlen=64 → 51f0bebf 7e3b9d92 fc497417 79363cfe
   - Expected: aes128_cmac_compute(_rfc4493_key(), _msg_64()) equals `_tag_64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Example 4: Mlen=64 → 51f0bebf 7e3b9d92 fc497417 79363cfe")
# 4 full blocks; exercises the K1 path with multiple CBC-MAC iterations.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_64())).to_equal(_tag_64())
```

</details>

### AES-128-CMAC RFC 4493 §2.5 verification

#### verify accepts the correct tag for each §4 example

- verify accepts the correct tag for each §4 example
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty()) is true
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_16(), _tag_16()) is true
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_40(), _tag_40()) is true
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_64(), _tag_64()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify accepts the correct tag for each §4 example")
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_16(), _tag_16())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_40(), _tag_40())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_64(), _tag_64())).to_equal(true)
```

</details>

#### verify rejects a single-bit-flipped tag (CT-compare property)

- verify rejects a single-bit-flipped tag (CT-compare property)
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty_bit_flipped()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify rejects a single-bit-flipped tag (CT-compare property)")
# Even one bit's difference from the correct tag must cause rejection.
# Constant-time XOR-OR accumulator must catch this, not early-exit.
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty_bit_flipped())).to_equal(false)
```

</details>

#### verify rejects a length-mismatched (truncated) tag

- verify rejects a length-mismatched (truncated) tag
   - Expected: aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_short()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify rejects a length-mismatched (truncated) tag")
# An 8-byte tag is half-length; the length check must reject up-front.
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_short())).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-128-CMAC RFC 4493 §2.3 subkey generation, AES-128-CMAC RFC 4493 §4 generation vectors, AES-128-CMAC RFC 4493 §2.5 verification.
- AES-128-CMAC RFC 4493 §2.3 subkey generation
- AES-128-CMAC RFC 4493 §4 generation vectors
- AES-128-CMAC RFC 4493 §2.5 verification

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37d9b261e60c49a8c51d2c023d9a0a334d1a7c082afc6a7693f44ae1279bfb28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37d9b261e60c49a8c51d2c023d9a0a334d1a7c082afc6a7693f44ae1279bfb28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37d9b261e60c49a8c51d2c023d9a0a334d1a7c082afc6a7693f44ae1279bfb28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'K1 matches RFC 4493 §4 reference (fbeed618…)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'K2 matches RFC 4493 §4 reference (f7ddac30…)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Example 1: Mlen=0 → bb1d6929 e9593728 7fa37d12 9b756746' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
