# @manual: primary

> Purpose: Prove that SM3 — GB/T 32905-2012 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that SM3 — GB/T 32905-2012 known-answer vectors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/sm3_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SM3 — GB/T 32905-2012 known-answer vectors.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-CRYPTO-001
doc/01_research/local/REQ-OS-CRYPTO-001.md
doc/03_plan/sys_test/REQ-OS-CRYPTO-001.md
doc/04_architecture/REQ-OS-CRYPTO-001.md
doc/05_design/REQ-OS-CRYPTO-001.md

## Scenarios

### SM3 — GB/T 32905-2012 known-answer vectors

#### SM3(\

- SM3(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM3(\")
expect(_bytes_hex(sm3_hash(_abc_bytes()))).to_equal(
    "66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0"
)
```

</details>

#### SM3(\

- SM3(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM3(\")
expect(_bytes_hex(sm3_hash(_abcd16_bytes()))).to_equal(
    "debe9ff92275b8a138604889c18e5a4d6fdb70e5387e5765293dcba39c0c5732"
)
```

</details>

#### SM3(\

- SM3(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM3(\")
expect(_bytes_hex(sm3_hash(_empty_bytes()))).to_equal(
    "1ab21d8355cfa17f8e61194831e81a8f22bec8c728fefb747ed035eb5082aa2b"
)
```

</details>

#### SM3 digest length is 32 bytes

- Verify: SM3 digest length is 32 bytes
   - Expected: sm3_hash(_empty_bytes()).len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Verify: SM3 digest length is 32 bytes")
expect(sm3_hash(_empty_bytes()).len()).to_equal(32)  # oracle: 32 — named expected value from the requirement
```

</details>

#### SM3 padding produces multiple-of-64 length

- Verify: SM3 padding produces multiple-of-64 length
   - Expected: sm3_pad(_abc_bytes()).len() % 64 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Verify: SM3 padding produces multiple-of-64 length")
expect(sm3_pad(_abc_bytes()).len() % 64).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### sm3_compress accepts IV state and 64-byte block and returns 8 words

- Verify: sm3_compress accepts IV state and 64-byte block and returns 8 words
   - Expected: result.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Verify: sm3_compress accepts IV state and 64-byte block and returns 8 words")
var block: [u8] = []
var bi = 0
while bi < 64:
    block.push(0x00)
    bi = bi + 1
var state_iv = []
state_iv.push(0x7380166F)
state_iv.push(0x4914B2B9)
state_iv.push(0x172442D7)
state_iv.push(0xDA8A0600)
state_iv.push(0xA96F30BC)
state_iv.push(0x163138AA)
state_iv.push(0xE38DEE4D)
state_iv.push(0xB0FB0E4E)
val result = sm3_compress(state_iv, block)
expect(result.len()).to_equal(8)  # oracle: 8 — named expected value from the requirement
```

</details>

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
- `REQ-OS-CRYPTO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22206271dd60cd74fc86dcc41b9d97f5cfd6590a4e5898b26bebd46587f442e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22206271dd60cd74fc86dcc41b9d97f5cfd6590a4e5898b26bebd46587f442e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22206271dd60cd74fc86dcc41b9d97f5cfd6590a4e5898b26bebd46587f442e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/sm3_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/sm3_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/sm3_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/sm3_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/sm3_kat_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM3(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sm3_kat_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM3(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sm3_kat_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM3(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
