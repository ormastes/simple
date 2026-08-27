# Check Entry Target Routing Contract Specification

> Tests covering check entry target routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Check Entry Target Routing Contract Specification

## Scenarios

### check entry target routing

#### does not classify the reserved-looking target basename as argv metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not classify the reserved-looking target basename as argv metadata
   - Expected: source does not contain `arg.ends_with("check_entry.spl")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not classify the reserved-looking target basename as argv metadata")
val source = file_read("src/app/cli/check_entry.spl")
expect(source).to_contain("if i == 0 and arg == \"check\":")
# Was `to_contain("a source")`, which matched only the rationale
# comment. Anchored instead to the real consume-then-continue body:
# nothing but an exact leading "check" token may be dropped.
expect(source).to_contain("if i == 0 and arg == \"check\":\n            i = i + 1\n            continue\n        out.push(arg)")
expect(source.contains("arg.ends_with(\"check_entry.spl\")")).to_equal(false)
```

</details>

#### still consumes the explicit adjacent check command discriminator

- still consumes the explicit adjacent check command discriminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still consumes the explicit adjacent check command discriminator")
val source = file_read("src/app/cli/check_entry.spl")
expect(source).to_contain("i == 0 and arg == \"check\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering check entry target routing.
- check entry target routing

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

- Canonical SPipe generation for source `5e031a33cd72ae9a244973993b9b723d43372b315e13acff0df0316e9926f5e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e031a33cd72ae9a244973993b9b723d43372b315e13acff0df0316e9926f5e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e031a33cd72ae9a244973993b9b723d43372b315e13acff0df0316e9926f5e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not classify the reserved-looking target basename as argv metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still consumes the explicit adjacent check command discriminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
