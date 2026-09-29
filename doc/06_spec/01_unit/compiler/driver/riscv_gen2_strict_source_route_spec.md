# riscv_gen2_strict_source_route_spec

> Direct compiler-driver oracle for fail-closed critical Gen2 source routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_gen2_strict_source_route_spec

Direct compiler-driver oracle for fail-closed critical Gen2 source routing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct compiler-driver oracle for fail-closed critical Gen2 source routing.

The public source facade retains a legacy subset fallback, so this focused unit
specification invokes `CompilerDriver` directly and observes only its compiler
result and emitted artifact boundary.

## Scenarios

- should require an explicit critical target before legacy VHDL emission
- should reject an unsupported target before any VHDL artifact exists
- should reject unsupported strict HWIR source without falling back to legacy VHDL

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4492bc77438db93328352cde79e1628599db53275d969e75797c260696fe6f38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4492bc77438db93328352cde79e1628599db53275d969e75797c260696fe6f38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4492bc77438db93328352cde79e1628599db53275d969e75797c260696fe6f38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require an explicit critical target before legacy VHDL emission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require an explicit critical target before legacy VHDL emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unsupported target before any VHDL artifact exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an unsupported target before any VHDL artifact exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported strict HWIR source without falling back to legacy VHDL' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unsupported strict HWIR source without falling back to legacy VHDL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
