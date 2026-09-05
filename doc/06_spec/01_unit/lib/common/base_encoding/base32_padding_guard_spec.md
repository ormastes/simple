# Base32 Padding Guard Specification

> Tests covering base32 padding guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base32 Padding Guard Specification

## Scenarios

### base32 padding guards

#### keeps valid padded standard base32 decode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid padded standard base32 decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid padded standard base32 decode")
assert_equal(bytes_to_text(base32_decode("MY======")), "f")
```

</details>

#### keeps valid padded base32hex decode

- keeps valid padded base32hex decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid padded base32hex decode")
assert_equal(bytes_to_text(base32_decode_hex("CO======")), "f")
```

</details>

#### rejects standard padding before enough data

- rejects standard padding before enough data


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects standard padding before enough data")
assert_equal(base32_decode("========").len(), 0)
assert_equal(base32_decode("M=======").len(), 0)
```

</details>

#### rejects standard data after padding

- rejects standard data after padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects standard data after padding")
assert_equal(base32_decode("MY=A").len(), 0)
```

</details>

#### rejects base32hex data after padding

- rejects base32hex data after padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects base32hex data after padding")
assert_equal(base32_decode_hex("CO=0").len(), 0)
```

</details>

#### rejects invalid standard unpadded final group lengths

- rejects invalid standard unpadded final group lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid standard unpadded final group lengths")
assert_equal(base32_decode("M").len(), 0)
assert_equal(base32_decode("MZX").len(), 0)
assert_equal(base32_decode("MZXW6Y").len(), 0)
```

</details>

#### rejects invalid base32hex unpadded final group lengths

- rejects invalid base32hex unpadded final group lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid base32hex unpadded final group lengths")
assert_equal(base32_decode_hex("C").len(), 0)
assert_equal(base32_decode_hex("CPN").len(), 0)
assert_equal(base32_decode_hex("CPNMUO").len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base32_padding_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base32 padding guards.
- base32 padding guards

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

- Canonical SPipe generation for source `030d890fbe16fd444324ef5cf4c8f70f6ab72f62535317da884d4ca7c75ca049`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `030d890fbe16fd444324ef5cf4c8f70f6ab72f62535317da884d4ca7c75ca049`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `030d890fbe16fd444324ef5cf4c8f70f6ab72f62535317da884d4ca7c75ca049`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/base_encoding/base32_padding_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base32_padding_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/base_encoding/base32_padding_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base32_padding_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base32_padding_guard_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid padded standard base32 decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base32_padding_guard_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid padded base32hex decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base32_padding_guard_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects standard padding before enough data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
