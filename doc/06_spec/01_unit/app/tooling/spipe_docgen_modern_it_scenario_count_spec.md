# Spipe Docgen Modern It Scenario Count Specification

> Tests covering validate_spec scenario counting, is_scenario_line.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Docgen Modern It Scenario Count Specification

## Scenarios

### validate_spec scenario counting

#### counts modern call-form scenarios

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts modern call-form scenarios
   - Expected: result.docs_present is true
   - Expected: result.doc_lines > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts modern call-form scenarios")
val src = "describe \"D\":\n" +
    "    it(\"does the thing\"):\n" +
    "        expect(1).to_equal(1)\n" +
    "    it(\"does the other thing\"):\n" +
    "        expect(2).to_equal(2)\n"
val result = validate_spec(_doc(src))
expect(result.docs_present).to_equal(true)
expect(result.doc_lines > 0).to_equal(true)
```

</details>

#### still counts legacy bare-form scenarios

- still counts legacy bare-form scenarios
   - Expected: result.docs_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still counts legacy bare-form scenarios")
val src = "describe \"D\":\n" +
    "    it \"does the thing\":\n" +
    "        expect(1).to_equal(1)\n"
val result = validate_spec(_doc(src))
expect(result.docs_present).to_equal(true)
```

</details>

#### control: a spec with no scenarios and no doc blocks is not docs_present

- control: a spec with no scenarios and no doc blocks is not docs_present
   - Expected: result.docs_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: a spec with no scenarios and no doc blocks is not docs_present")
val src = "fn helper() -> i64:\n    1\n"
val result = validate_spec(_doc(src))
expect(result.docs_present).to_equal(false)
```

</details>

### is_scenario_line

#### recognises the modern call form

- recognises the modern call form
   - Expected: is_scenario_line("it(\"x\"):") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises the modern call form")
expect(is_scenario_line("it(\"x\"):")).to_equal(true)
```

</details>

#### recognises the legacy bare form

- recognises the legacy bare form
   - Expected: is_scenario_line("it \"x\":") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises the legacy bare form")
expect(is_scenario_line("it \"x\":")).to_equal(true)
```

</details>

#### rejects a line that is not a scenario

- rejects a line that is not a scenario
   - Expected: is_scenario_line("val it = 3") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a line that is not a scenario")
expect(is_scenario_line("val it = 3")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering validate_spec scenario counting, is_scenario_line.
- validate_spec scenario counting
- is_scenario_line

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

- Canonical SPipe generation for source `0a1952694d09b91f674728edd0b398d4321a48c4d732018b19aa79ef500c6129`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a1952694d09b91f674728edd0b398d4321a48c4d732018b19aa79ef500c6129`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a1952694d09b91f674728edd0b398d4321a48c4d732018b19aa79ef500c6129`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts modern call-form scenarios' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still counts legacy bare-form scenarios' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: a spec with no scenarios and no doc blocks is not docs_present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
