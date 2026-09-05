# Serpent Kat Specification

> Tests covering Serpent KAT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serpent Kat Specification

## Scenarios

### Serpent KAT

#### enc zero/zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enc zero/zero
   - Expected: _t_enc_zero() equals `3620b17ae6a993d09618b8768266bae9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enc zero/zero")
expect(_t_enc_zero()).to_equal("3620b17ae6a993d09618b8768266bae9")
```

</details>

#### ct is 16 bytes

- ct is 16 bytes
   - Expected: _t_enc_zero_len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ct is 16 bytes")
expect(_t_enc_zero_len()).to_equal(16)
```

</details>

#### rt zero

- rt zero
   - Expected: _t_rt_zero() equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt zero")
expect(_t_rt_zero()).to_equal("00000000000000000000000000000000")
```

</details>

#### dec vec1

- dec vec1
   - Expected: _t_dec_vec1() equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dec vec1")
expect(_t_dec_vec1()).to_equal("00000000000000000000000000000000")
```

</details>

#### enc vec2

- enc vec2
   - Expected: _t_enc_vec2() equals `b2288b968ae8b08648d1ce9606fd992d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enc vec2")
expect(_t_enc_vec2()).to_equal("b2288b968ae8b08648d1ce9606fd992d")
```

</details>

#### dec vec2

- dec vec2
   - Expected: _t_dec_vec2() equals `d29d576fcea3a3a7ed9099f29273d78e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dec vec2")
expect(_t_dec_vec2()).to_equal("d29d576fcea3a3a7ed9099f29273d78e")
```

</details>

#### enc vec3

- enc vec3
   - Expected: _t_enc_vec3() equals `264e5481eff42a4606abda06c0bfda3d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enc vec3")
expect(_t_enc_vec3()).to_equal("264e5481eff42a4606abda06c0bfda3d")
```

</details>

#### dec vec3

- dec vec3
   - Expected: _t_dec_vec3() equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dec vec3")
expect(_t_dec_vec3()).to_equal("00000000000000000000000000000000")
```

</details>

#### rt 256

- rt 256
   - Expected: _t_rt_256() equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt 256")
expect(_t_rt_256()).to_equal("00000000000000000000000000000000")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/serpent_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Serpent KAT.
- Serpent KAT

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

- Canonical SPipe generation for source `8c942f3c36cbfedad0af1463e1317c4d303283c9d8fc48a333ded0a99f349938`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c942f3c36cbfedad0af1463e1317c4d303283c9d8fc48a333ded0a99f349938`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c942f3c36cbfedad0af1463e1317c4d303283c9d8fc48a333ded0a99f349938`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/serpent_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/serpent_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/serpent_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/serpent_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/serpent_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/serpent_kat_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enc zero/zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/serpent_kat_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ct is 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/serpent_kat_spec.spl:250:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
