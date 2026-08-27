# Ssh Ct Auth Compare Specification

> Tests covering A3 constant-time byte comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Ct Auth Compare Specification

## Scenarios

### A3 constant-time byte comparison

#### returns true for equal byte arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns true for equal byte arrays
   - Expected: _ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 3u8, 4u8]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for equal byte arrays")
expect(_ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 3u8, 4u8])).to_equal(true)
```

</details>

#### returns false when a single byte differs

- returns false when a single byte differs
   - Expected: _ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 9u8, 4u8]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when a single byte differs")
expect(_ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 9u8, 4u8])).to_equal(false)
```

</details>

#### returns false when the first byte differs

- returns false when the first byte differs
   - Expected: _ct_bytes_equal([9u8, 2u8, 3u8], [1u8, 2u8, 3u8]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when the first byte differs")
expect(_ct_bytes_equal([9u8, 2u8, 3u8], [1u8, 2u8, 3u8])).to_equal(false)
```

</details>

#### returns false on a length mismatch (shorter)

- returns false on a length mismatch (shorter)
   - Expected: _ct_bytes_equal([1u8, 2u8], [1u8, 2u8, 3u8]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a length mismatch (shorter)")
expect(_ct_bytes_equal([1u8, 2u8], [1u8, 2u8, 3u8])).to_equal(false)
```

</details>

#### returns false on a length mismatch (longer)

- returns false on a length mismatch (longer)
   - Expected: _ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 3u8]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a length mismatch (longer)")
expect(_ct_bytes_equal([1u8, 2u8, 3u8, 4u8], [1u8, 2u8, 3u8])).to_equal(false)
```

</details>

#### returns true for two empty arrays

- returns true for two empty arrays
   - Expected: _ct_bytes_equal([], []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for two empty arrays")
expect(_ct_bytes_equal([], [])).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering A3 constant-time byte comparison.
- A3 constant-time byte comparison

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

- Canonical SPipe generation for source `3c22b5010b5beb5ff070988819eb8c3cf228362ba8583ef0301dd4856495b2e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c22b5010b5beb5ff070988819eb8c3cf228362ba8583ef0301dd4856495b2e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c22b5010b5beb5ff070988819eb8c3cf228362ba8583ef0301dd4856495b2e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for equal byte arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when a single byte differs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when the first byte differs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
