# Native cross-module static error factory regression

> Reproduces the Stage 3 call shape where `BackendError.runtime_error(...)` was

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native cross-module static error factory regression

Reproduces the Stage 3 call shape where `BackendError.runtime_error(...)` was

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduces the Stage 3 call shape where `BackendError.runtime_error(...)` was
classified unresolved and its type-valued receiver crossed an aggregate native
call boundary. Acceptance requires a real native candidate and exact output.

## Scenarios

### REQ-BST-STATIC-001: native static-owner identity

#### should retain a type receiver across the native lowering boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-BST-STATIC-001
```

</details>

#### should preserve adjacent static methods on the same imported owner

- should preserve adjacent static methods on the same imported owner
- Execute runtime_error and type_error shaped factories


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve adjacent static methods on the same imported owner")
step("Execute runtime_error and type_error shaped factories")
expect(_static_factory_gate.0).to_contain("factories=2")
```

</details>

#### should reject shortcuts and missing native evidence

- should reject shortcuts and missing native evidence
- Require a pure-Simple compiler and an executed native candidate
   - Expected: _static_factory_gate.1 equals ``
   - Expected: _static_factory_gate.0 does not contain `STATUS: FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject shortcuts and missing native evidence")
step("Require a pure-Simple compiler and an executed native candidate")
expect(_static_factory_gate.1).to_equal("")
expect(_static_factory_gate.0.contains("STATUS: FAIL")).to_equal(false)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-BST-STATIC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ceb8bb79c8cfa957d97fea8b5f38f8d45f35935412fd7037581b990312fbd1d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ceb8bb79c8cfa957d97fea8b5f38f8d45f35935412fd7037581b990312fbd1d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ceb8bb79c8cfa957d97fea8b5f38f8d45f35935412fd7037581b990312fbd1d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl
mirror: doc/06_spec/03_system/compiler/native_crossmodule_static_error_factory_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_crossmodule_static_error_factory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_crossmodule_static_error_factory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should retain a type receiver across the native lowering boundary' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain a type receiver across the native lowering boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve adjacent static methods on the same imported owner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve adjacent static methods on the same imported owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject shortcuts and missing native evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject shortcuts and missing native evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
