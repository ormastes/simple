# Bootstrap Signature Source Specification

> Tests covering bootstrap MIR signature source shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Signature Source Specification

## Scenarios

### bootstrap MIR signature source shape

#### does not hardcode generic bootstrap stubs to i64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not hardcode generic bootstrap stubs to i64
   - Expected: source contains `me bootstrap_function_signature(name: text) -> MirSignature:`
   - Expected: source contains `val signature = self.bootstrap_function_signature(name)`
   - Expected: source does not contain `val signature = MirSignature(params: [], return_type: MirType.i64(), is_varia... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not hardcode generic bootstrap stubs to i64")
val source = module_lowering_source()
expect(source.contains("me bootstrap_function_signature(name: text) -> MirSignature:")).to_equal(true)
expect(source.contains("val signature = self.bootstrap_function_signature(name)")).to_equal(true)
expect(source.contains("val signature = MirSignature(params: [], return_type: MirType.i64(), is_variadic: false)\n        var bldr = self.builder\n        bldr.begin_function(symbol, name, signature")).to_equal(false)
```

</details>

#### returns typed zero for non-unit bootstrap fallback results

- returns typed zero for non-unit bootstrap fallback results
   - Expected: source contains `fn bootstrap_default_return_operand(return_type: MirType) -> MirOperand?:`
   - Expected: source contains `MirConstValue.Zero, return_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns typed zero for non-unit bootstrap fallback results")
val source = module_lowering_source()
expect(source.contains("fn bootstrap_default_return_operand(return_type: MirType) -> MirOperand?:")).to_equal(true)
expect(source.contains("MirConstValue.Zero, return_type")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap MIR signature source shape.
- bootstrap MIR signature source shape

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2801f4b443385299cbeac2d0c304afc4ec7a0ae29a9fe442228ccb0d8286b470`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2801f4b443385299cbeac2d0c304afc4ec7a0ae29a9fe442228ccb0d8286b470`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2801f4b443385299cbeac2d0c304afc4ec7a0ae29a9fe442228ccb0d8286b470`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/bootstrap_signature_source_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/bootstrap_signature_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/bootstrap_signature_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not hardcode generic bootstrap stubs to i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns typed zero for non-unit bootstrap fallback results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
