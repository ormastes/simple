# Claude Full Sentry Error Boundary

> Checks children render before errors and null render after errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Sentry Error Boundary

Checks children render before errors and null render after errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks children render before errors and null render after errors.

## Scenarios

### Claude full SentryErrorBoundary

#### renders children until an error is captured

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders children until an error is captured
- Initial state has no error and renders children
   - Expected: boundary.hasError equals `initialHasError()`
   - Expected: boundary.render() equals `child`
   - Expected: boundary.hasError equals `errorStateHasError()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders children until an error is captured")
step("Initial state has no error and renders children")
val boundary = SentryErrorBoundary.new("child")
expect(boundary.hasError).to_equal(initialHasError())
expect(boundary.render()).to_equal("child")
boundary.captureError()
expect(boundary.hasError).to_equal(errorStateHasError())
expect(boundary.render()).to_be_nil()
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin boundary behavior
   - Expected: rendersNullAfterError() is true
   - Expected: rendersChildrenBeforeError() is true
   - Expected: sentryErrorBoundarySourceLinesModeled() equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin boundary behavior")
expect(rendersNullAfterError()).to_equal(true)
expect(rendersChildrenBeforeError()).to_equal(true)
expect(sentryErrorBoundarySourceLinesModeled()).to_equal(26)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4b8f8cab1b8be5650094db03bb175f72127eceec4d7b70cac06531771d17f9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4b8f8cab1b8be5650094db03bb175f72127eceec4d7b70cac06531771d17f9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4b8f8cab1b8be5650094db03bb175f72127eceec4d7b70cac06531771d17f9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders children until an error is captured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports source-backed constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
