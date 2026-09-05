# Backend Basic Specification

> Tests covering Backend Basic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Basic Specification

## Scenarios

### Backend Basic

#### creates a builder with default metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a builder with default metadata
   - Expected: builder.test_name equals `basic`
   - Expected: builder.instructions.len() equals `0`
   - Expected: builder.next_vreg equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a builder with default metadata")
val builder = new_builder("basic")

expect(builder.test_name).to_equal("basic")
expect(builder.instructions.len()).to_equal(0)
expect(builder.next_vreg).to_equal(0)
```

</details>

#### tracks registers and preserves backend selection

- tracks registers and preserves backend selection
   - Expected: builder.next_vreg equals `5`
   - Expected: test_case.name equals `tracked`
   - Expected: test_case.instructions.len() equals `3`
   - Expected: test_case.expected_backends.len() equals `1`
   - Expected: test_case.expected_backends[0] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks registers and preserves backend selection")
val builder = new_builder("tracked")
builder.add_const_int(0, 42)
builder.add_const_int(3, 7)
builder.add_add(4, 0, 3)
builder.only_backend(BackendTarget.Interpreter)

val test_case = builder.build()

expect(builder.next_vreg).to_equal(5)
expect(test_case.name).to_equal("tracked")
expect(test_case.instructions.len()).to_equal(3)
expect(test_case.expected_backends.len()).to_equal(1)
expect(test_case.expected_backends[0]).to_equal(BackendTarget.Interpreter)
```

</details>

#### builds the canned arithmetic helper

- builds the canned arithmetic helper
   - Expected: test_case.name equals `simple_arithmetic`
   - Expected: test_case.instructions.len() equals `4`
   - Expected: test_case.expected_backends.len() equals `3`
   - Expected: test_case.expected_backends[0] equals `BackendTarget.Cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the canned arithmetic helper")
val test_case = simple_arithmetic()

expect(test_case.name).to_equal("simple_arithmetic")
expect(test_case.instructions.len()).to_equal(4)
expect(test_case.expected_backends.len()).to_equal(3)
expect(test_case.expected_backends[0]).to_equal(BackendTarget.Cranelift)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/backend_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Basic.
- Backend Basic

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `edf689fa106d4b923cbd0a059db295ba8a29dcecbbcfbae1dcc6fc9d3062e9bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edf689fa106d4b923cbd0a059db295ba8a29dcecbbcfbae1dcc6fc9d3062e9bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edf689fa106d4b923cbd0a059db295ba8a29dcecbbcfbae1dcc6fc9d3062e9bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/backend_basic_spec.spl
mirror: doc/06_spec/unit/compiler/backend/backend_basic_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/backend_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/backend_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/backend_basic_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/backend_basic_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a builder with default metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_basic_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks registers and preserves backend selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_basic_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the canned arithmetic helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
