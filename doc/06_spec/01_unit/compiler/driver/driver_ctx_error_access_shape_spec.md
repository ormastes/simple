# Driver Ctx Error Access Shape Specification

> Tests covering driver compiler-context error access shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Ctx Error Access Shape Specification

## Scenarios

### driver compiler-context error access shape

#### exposes a method-shaped accessor on the context owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes a method-shaped accessor on the context owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("exposes a method-shaped accessor on the context owner")
val types = file_read("src/compiler/80.driver/driver_types.spl")
expect(types).to_contain("fn error_message_at(index: i64) -> text:")
```

</details>

#### never direct-indexes ctx.errors in any driver phase file

- never direct-indexes ctx.errors in any driver phase file
   - Expected: offenders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never direct-indexes ctx.errors in any driver phase file")
var offenders: [text] = []
var f = 0
while f < DRIVER_FILES.len():
    val path = DRIVER_FILES[f]
    val source = file_read(path)
    if source.contains("ctx.errors["):
        offenders.push(path)
    f = f + 1
expect(offenders.len()).to_equal(0)
```

</details>

#### uses the accessor at the phase-3 failure sites

- uses the accessor at the phase-3 failure sites


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the accessor at the phase-3 failure sites")
val orch = file_read(DRIVER_FILES[0])
expect(orch).to_contain("self.ctx.error_message_at(0)")
expect(orch).to_contain("self.ctx.error_message_at(phase3_error_index)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver compiler-context error access shape.
- driver compiler-context error access shape

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d505acab1303c3290c3a16dcf3fe82d7b0ddd21f405847e6f559f85f8d1320a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d505acab1303c3290c3a16dcf3fe82d7b0ddd21f405847e6f559f85f8d1320a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d505acab1303c3290c3a16dcf3fe82d7b0ddd21f405847e6f559f85f8d1320a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a method-shaped accessor on the context owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never direct-indexes ctx.errors in any driver phase file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_ctx_error_access_shape_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the accessor at the phase-3 failure sites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
