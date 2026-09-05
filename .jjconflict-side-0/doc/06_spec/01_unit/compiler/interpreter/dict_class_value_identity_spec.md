# Dict Class Value Identity Specification

> Tests covering class instances reached through a container keep their identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Class Value Identity Specification

## Scenarios

### class instances reached through a container keep their identity

#### persists a mutation made through Dict.get without a manual write-back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- persists a mutation made through Dict.get without a manual write-back
- Run the run-path probe under the default engine
- The report's own repro sketch: set, get, mutate, get again
- Key type must not change value semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists a mutation made through Dict.get without a manual write-back")
step("Run the run-path probe under the default engine")
val jit = run_probe_in_mode("jit")

step("The report's own repro sketch: set, get, mutate, get again")
expect(jit).to_contain("PASS dict_get_mutate_int")
expect(jit).to_contain("PASS dict_get_mutate_text")

step("Key type must not change value semantics")
expect(jit).to_contain("PASS dict_text_key")
```

</details>

#### persists a mutation made inside a callee through a dict-valued field

- persists a mutation made inside a callee through a dict-valued field
- This is the shape the filed cache actually had, and the frame boundary the copy-on-write family died at


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists a mutation made inside a callee through a dict-valued field")
step("This is the shape the filed cache actually had, and the frame boundary the copy-on-write family died at")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS callee_field_dict_hits")
expect(jit).to_contain("PASS callee_field_dict_last")
```

</details>

#### keeps identity through other container kinds, not just Dict.get

- keeps identity through other container kinds, not just Dict.get
- An array element is the same reference-identity question
- Two reads of one key must alias the same object, not yield two copies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps identity through other container kinds, not just Dict.get")
step("An array element is the same reference-identity question")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS array_elem_identity")

step("Two reads of one key must alias the same object, not yield two copies")
expect(jit).to_contain("PASS two_handles_alias")
```

</details>

#### behaves identically on both engines and reports no failure

- behaves identically on both engines and reports no failure
- Collect both engines' output
- Both must reach the aggregate verdict
- No individual check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("behaves identically on both engines and reports no failure")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("Both must reach the aggregate verdict")
expect(interp).to_contain("DICT_CLASS_IDENTITY PROBE: ALL PASS")
expect(jit).to_contain("DICT_CLASS_IDENTITY PROBE: ALL PASS")

step("No individual check may have failed under either engine")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering class instances reached through a container keep their identity.
- class instances reached through a container keep their identity

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff66522fa8f245f0f932e0d2157aaaac6c52d6cf17f691c0ab88895957bec442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff66522fa8f245f0f932e0d2157aaaac6c52d6cf17f691c0ab88895957bec442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff66522fa8f245f0f932e0d2157aaaac6c52d6cf17f691c0ab88895957bec442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/dict_class_value_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/dict_class_value_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/dict_class_value_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists a mutation made through Dict.get without a manual write-back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists a mutation made inside a callee through a dict-valued field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps identity through other container kinds, not just Dict.get' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
