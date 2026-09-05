# Lshr64 Debug Specification

> Tests covering lshr64 debug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lshr64 Debug Specification

## Scenarios

### lshr64 debug

#### sha512 bytes([0x61]) gets some output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sha512 bytes([0x61]) gets some output
   - Expected: r.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha512 bytes([0x61]) gets some output")
val r = sha512_bytes([0x61])
expect(r.len()).to_equal(64)
```

</details>

#### sha512 empty output length

- sha512 empty output length
   - Expected: r.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha512 empty output length")
val r = sha512_bytes([])
expect(r.len()).to_equal(64)
```

</details>

#### empty first byte should be 0xcf

- empty first byte should be 0xcf
   - Expected: r[0] equals `0xcf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty first byte should be 0xcf")
val r = sha512_bytes([])
expect(r[0]).to_equal(0xcf)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/crypto/lshr64_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lshr64 debug.
- lshr64 debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `db48ce963f2ffb7b67521d1d326b4b3a43d8ae2bf7fdc0f3bdf5cd45db9239ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db48ce963f2ffb7b67521d1d326b4b3a43d8ae2bf7fdc0f3bdf5cd45db9239ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db48ce963f2ffb7b67521d1d326b4b3a43d8ae2bf7fdc0f3bdf5cd45db9239ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/crypto/lshr64_debug_spec.spl
mirror: doc/06_spec/unit/lib/common/crypto/lshr64_debug_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/crypto/lshr64_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/crypto/lshr64_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/crypto/lshr64_debug_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/crypto/lshr64_debug_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sha512 bytes([0x61]) gets some output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/lshr64_debug_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sha512 empty output length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/lshr64_debug_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty first byte should be 0xcf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
