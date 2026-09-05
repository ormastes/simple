# Mir Json Signature Source Specification

> Tests covering MIR JSON signature source shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Json Signature Source Specification

## Scenarios

### MIR JSON signature source shape

#### emits explicit null for missing signature return metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits explicit null for missing signature return metadata
   - Expected: source contains `if sig.return_type == nil:`
   - Expected: source contains `\\"return_type\\":null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits explicit null for missing signature return metadata")
val source = mir_json_source()
expect(source.contains("if sig.return_type == nil:")).to_equal(true)
expect(source.contains("\\\"return_type\\\":null")).to_equal(true)
```

</details>

#### keeps CallIndirect on shared signature serialization

- keeps CallIndirect on shared signature serialization
   - Expected: source contains `case CallIndirect`
   - Expected: source contains `val sig = serialize_mir_signature(signature)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps CallIndirect on shared signature serialization")
val source = mir_json_source()
expect(source.contains("case CallIndirect")).to_equal(true)
expect(source.contains("val sig = serialize_mir_signature(signature)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_json_signature_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR JSON signature source shape.
- MIR JSON signature source shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6a7e50ca68ce5afa1c9d428830fce027ad8b109494351ec8b89a894b03ef55f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6a7e50ca68ce5afa1c9d428830fce027ad8b109494351ec8b89a894b03ef55f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6a7e50ca68ce5afa1c9d428830fce027ad8b109494351ec8b89a894b03ef55f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/mir_json_signature_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_json_signature_source_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/mir_json_signature_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_json_signature_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_json_signature_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/mir_json_signature_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/mir_json_signature_source_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits explicit null for missing signature return metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_json_signature_source_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CallIndirect on shared signature serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
