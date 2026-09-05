# X25519mlkem768 Simd Dispatch Structure Specification

> Tests covering X25519MLKEM768 SIMD dispatch structure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Simd Dispatch Structure Specification

## Scenarios

### X25519MLKEM768 SIMD dispatch structure

#### should dispatch once per butterfly group and preserve scalar tails (NFR-010)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should dispatch once per butterfly group and preserve scalar tails (NFR-010)
- Inspect AVX2 NEON and RVV group loops and receipt accounting
   - Expected: source does not contain `int remaining = start + len - j;`
   - Expected: source does not contain `int width = 0;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should dispatch once per butterfly group and preserve scalar tails (NFR-010)")
step("Inspect AVX2 NEON and RVV group loops and receipt accounting")
val source = file_read_text("src/runtime/runtime_simd_dispatch.c")
expect(source).to_contain("const int end = start + len;")
expect(source).to_contain("if (backend == 1) {\n                while (j + 8 <= end)")
expect(source).to_contain("if (backend == 2) {\n                while (j + 4 <= end)")
expect(source).to_contain("if (backend == 3 && j < end)")
expect(source).to_contain("(size_t)(end - j)")
expect(source).to_contain("hits += executed_chunks;")
expect(source).to_contain("while (j < end) {")
expect(source).to_contain("if (j >= end) continue;")
expect(source.contains("int remaining = start + len - j;")).to_equal(false)
expect(source.contains("int width = 0;")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD dispatch structure.
- X25519MLKEM768 SIMD dispatch structure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86020ab973bc763f6f151f244987c9e09ff05530e0cd536c4bebe92c0bfc9621`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86020ab973bc763f6f151f244987c9e09ff05530e0cd536c4bebe92c0bfc9621`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86020ab973bc763f6f151f244987c9e09ff05530e0cd536c4bebe92c0bfc9621`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=95 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl:17:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should dispatch once per butterfly group and preserve scalar tails (NFR-010)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should dispatch once per butterfly group and preserve scalar tails (NFR-010)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
