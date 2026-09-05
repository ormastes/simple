# bootstrap_llvm_call_dest_definition_spec

> Purpose: This spec proves REQ-BSLLVM-001: Bootstrap LLVM call destinations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bootstrap_llvm_call_dest_definition_spec

Purpose: This spec proves REQ-BSLLVM-001: Bootstrap LLVM call destinations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves REQ-BSLLVM-001: Bootstrap LLVM call destinations.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### REQ-BSLLVM-001: Bootstrap LLVM call destinations

#### should define direct-call destinations before later uses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Lower a direct call with a used destination
- Inspect the emitted LLVM SSA definition
   - Expected: count_local_definitions(ir, "%l0") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BSLLVM-001
step("Lower a direct call with a used destination")
val body = make_call_destination_function(false)
val ir = emit_llvm_for_call_destination(body)

step("Inspect the emitted LLVM SSA definition")
expect(count_local_definitions(ir, "%l0")).to_equal(1)
expect(local_defined_before_first_use(ir, "%l0")).to_be(true)
```

</details>

#### should define indirect-call destinations before later uses

- should define indirect-call destinations before later uses
- Lower an indirect call with a used destination
- Inspect the emitted LLVM SSA definition
   - Expected: count_local_definitions(ir, "%l1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should define indirect-call destinations before later uses")
step("Lower an indirect call with a used destination")
val body = make_call_destination_function(true)
val ir = emit_llvm_for_call_destination(body)

step("Inspect the emitted LLVM SSA definition")
expect(count_local_definitions(ir, "%l1")).to_equal(1)
expect(local_defined_before_first_use(ir, "%l1")).to_be(true)
```

</details>

#### should reject a referenced call destination that was not emitted

- should reject a referenced call destination that was not emitted
- Attempt to lower an unsupported call payload
- Verify missing destinations fail before LLVM assembly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should reject a referenced call destination that was not emitted")
step("Attempt to lower an unsupported call payload")
val rejected = missing_destination_rejected()

step("Verify missing destinations fail before LLVM assembly")
expect(rejected).to_be(true)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-BSLLVM-001:`
- `REQ-BSLLVM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `355427158e3ae4a1a68ec582b61354a59593a5f55952517b4394909af916f480`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `355427158e3ae4a1a68ec582b61354a59593a5f55952517b4394909af916f480`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `355427158e3ae4a1a68ec582b61354a59593a5f55952517b4394909af916f480`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl
mirror: doc/06_spec/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:148:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define direct-call destinations before later uses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define direct-call destinations before later uses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define indirect-call destinations before later uses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define indirect-call destinations before later uses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:169:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a referenced call destination that was not emitted' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/compiler/bootstrap_llvm_call_dest_definition_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a referenced call destination that was not emitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
