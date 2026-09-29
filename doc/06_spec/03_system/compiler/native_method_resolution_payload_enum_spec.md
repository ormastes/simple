# Native method-resolution payload enum regression

> This scenario compiles and executes a standalone native fixture. It reproduces

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native method-resolution payload enum regression

This scenario compiles and executes a standalone native fixture. It reproduces

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_method_resolution_payload_enum_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This scenario compiles and executes a standalone native fixture. It reproduces
the Stage3 failure shape where an unresolved method-resolution enum was read
through the interpreter tagged-Any discriminant ABI, corrupting static-owner
recovery and the receiver local. The Rust seed is rejected as test authority.

## Scenarios

### REQ-BST-ENUM-001: native method-resolution payload integrity

#### should preserve every adjacent payload-enum shape in native execution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-BST-ENUM-001
```

</details>

#### should preserve static factory owner recovery in native execution

- should preserve static factory owner recovery in native execution
- Exercise a static factory call shaped like BackendError.type_error
   - Expected: _native_gate.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve static factory owner recovery in native execution")
step("Exercise a static factory call shaped like BackendError.type_error")
expect(_native_gate.2).to_equal(0)
expect(_native_gate.0).to_contain("static-factory=pass")
```

</details>

#### should preserve inferred array push receiver lowering

- should preserve inferred array push receiver lowering
- Exercise push on an initially empty inferred array
   - Expected: _native_gate.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve inferred array push receiver lowering")
step("Exercise push on an initially empty inferred array")
expect(_native_gate.2).to_equal(0)
expect(_native_gate.0).to_contain("inferred-push=pass")
```

</details>

#### should infer every scalar and folded-binary module constant

- should infer every scalar and folded-binary module constant
- Compile inferred module constants without reclassifying folded payloads
   - Expected: _native_gate.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should infer every scalar and folded-binary module constant")
step("Compile inferred module constants without reclassifying folded payloads")
expect(_native_gate.2).to_equal(0)
expect(_native_gate.0).to_contain("constant-inference=pass")
```

</details>

#### should fail closed when native compilation or execution is unavailable

- should fail closed when native compilation or execution is unavailable
- Require a real native candidate and an explicit probe verdict
   - Expected: _native_gate.1 equals ``
   - Expected: _native_gate.0 does not contain `STATUS: FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed when native compilation or execution is unavailable")
step("Require a real native candidate and an explicit probe verdict")
expect(_native_gate.1).to_equal("")
expect(_native_gate.0.contains("STATUS: FAIL")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-BST-ENUM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6296d48e02e96b4eac782226252502cee964d9109e5e57adfc409c1921cd3f6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6296d48e02e96b4eac782226252502cee964d9109e5e57adfc409c1921cd3f6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6296d48e02e96b4eac782226252502cee964d9109e5e57adfc409c1921cd3f6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/03_system/compiler/native_method_resolution_payload_enum_spec.spl
mirror: doc/06_spec/03_system/compiler/native_method_resolution_payload_enum_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=65 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_method_resolution_payload_enum_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_method_resolution_payload_enum_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:28:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should preserve every adjacent payload-enum shape in native execution' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve every adjacent payload-enum shape in native execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve static factory owner recovery in native execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve static factory owner recovery in native execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve inferred array push receiver lowering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve inferred array push receiver lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should infer every scalar and folded-binary module constant' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should infer every scalar and folded-binary module constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_method_resolution_payload_enum_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when native compilation or execution is unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
