# Mir Call Destination Shared Binding Contract Specification

> Tests covering MIR call destination strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Call Destination Shared Binding Contract Specification

## Scenarios

### MIR call destination strict shared bindings

#### builds direct and indirect optional destinations as values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds direct and indirect optional destinations as values
   - Expected: source.count(immutable_dest) equals `2`
   - Expected: source does not contain `var dest: LocalId? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds direct and indirect optional destinations as values")
val source = file_read("src/compiler/50.mir/mir_data.spl")
val immutable_dest = "val dest: LocalId? = if return_type.kind != MirTypeKind.Unit: self.new_temp(return_type) else: nil"

expect(source.count(immutable_dest)).to_equal(2)
expect(source.contains("var dest: LocalId? = nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR call destination strict shared bindings.
- MIR call destination strict shared bindings

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c1df40c7d3e795b99c33c709518066df52a127dc6a8a962e10538c4cef9bfa9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c1df40c7d3e795b99c33c709518066df52a127dc6a8a962e10538c4cef9bfa9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c1df40c7d3e795b99c33c709518066df52a127dc6a8a962e10538c4cef9bfa9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds direct and indirect optional destinations as values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
