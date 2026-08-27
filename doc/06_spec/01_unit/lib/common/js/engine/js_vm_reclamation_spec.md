# Js Vm Reclamation Specification

> Tests covering JavaScript VM lexical environment prerequisite, REQ-WEB-BROWSER-017: lexical parents preserve closure state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Vm Reclamation Specification

## Scenarios

### JavaScript VM lexical environment prerequisite

### REQ-WEB-BROWSER-017: lexical parents preserve closure state

#### should create a valid lexical parent chain
#### should retain captured object identity after the creator returns

- should retain captured object identity after the creator returns
- Capture a value in an escaped closure
   - Expected: check_escaped_closure_identity() equals `same`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should retain captured object identity after the creator returns")
step("Capture a value in an escaped closure")
expect(check_escaped_closure_identity()).to_equal("same")
```

</details>

#### should resolve shadowing and assign through the nearest lexical owner

- should resolve shadowing and assign through the nearest lexical owner
- Shadow and assign through the chain
   - Expected: values equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should resolve shadowing and assign through the nearest lexical owner")
step("Shadow and assign through the chain")
val fixture = setup_lexical_parent_fixture()
val values = check_parent_lookup_and_assignment(fixture)
expect(values).to_equal([
    "global",
    "child",
    "updated-child",
    "parent",
    "updated-creator",
    "updated-global",
    "local",
    "<missing>"
])
var stack = fixture.stack
expect(stack.get_var(fixture.escaped_env, "missing")).to_be_nil()
```

</details>

#### should reject a self-parent and terminate a corrupted cycle

- should reject a self-parent and terminate a corrupted cycle
- Reject a cyclic environment link
   - Expected: check_environment_cycle_rejected() equals `[-1, 1, 1, -1, -1, 8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a self-parent and terminate a corrupted cycle")
step("Reject a cyclic environment link")
expect(check_environment_cycle_rejected()).to_equal([-1, 1, 1, -1, -1, 8])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JavaScript VM lexical environment prerequisite, REQ-WEB-BROWSER-017: lexical parents preserve closure state.
- JavaScript VM lexical environment prerequisite
- REQ-WEB-BROWSER-017: lexical parents preserve closure state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-WEB-BROWSER-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `855e04efcb71bd3e8f2724dc5ffcb07ea9059ffd9f281e970babefd69ca7e9b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `855e04efcb71bd3e8f2724dc5ffcb07ea9059ffd9f281e970babefd69ca7e9b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `855e04efcb71bd3e8f2724dc5ffcb07ea9059ffd9f281e970babefd69ca7e9b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl
mirror: doc/06_spec/01_unit/lib/common/js/engine/js_vm_reclamation_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/js/engine/js_vm_reclamation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/js/engine/js_vm_reclamation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:114:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should create a valid lexical parent chain' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create a valid lexical parent chain' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain captured object identity after the creator returns' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain captured object identity after the creator returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:133:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve shadowing and assign through the nearest lexical owner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve shadowing and assign through the nearest lexical owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:152:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a self-parent and terminate a corrupted cycle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/js/engine/js_vm_reclamation_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a self-parent and terminate a corrupted cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
