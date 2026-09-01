# sffi_v2_p0_fail_closed_spec

> SFFI v2 P0 fail-closed executable probes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sffi_v2_p0_fail_closed_spec

SFFI v2 P0 fail-closed executable probes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SFFI v2 P0 fail-closed executable probes.

These scenarios invoke the deployed pure-Simple compiler in fresh subprocesses.
They prove runtime behavior, not source shape. A missing non-optional return and
an unresolved dynamic extern must fail with diagnostics and must not become a
fabricated value. Adjacent legal unit fallthrough and explicit optional absence
remain successful controls.

The scenarios are intentionally source-independent: their assertions observe
only process exit status and public diagnostics/output from executable probes.

## Scenarios

### SFFI v2 P0 fail-closed behavior

### REQ-SFFI-V2-001/002: declared return contracts distinguish and reject missing values

#### should reject fallthrough from a non-optional text function
#### should allow a unit function to fall through

- should allow a unit function to fall through
- Run a unit-returning function whose body falls through
- Confirm unit fallthrough completes normally
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow a unit function to fall through")
step("Run a unit-returning function whose body falls through")
val result = run_probe("sffi_v2_unit_fallthrough_probe.spl")
step("Confirm unit fallthrough completes normally")
expect(result.2).to_equal(0)
expect(result.0).to_contain("UNIT_OK")
```

</details>

#### should preserve explicitly returned optional absence

- should preserve explicitly returned optional absence
- Run an optional text function that explicitly returns nil
- Confirm explicit absence remains a successful None result
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve explicitly returned optional absence")
step("Run an optional text function that explicitly returns nil")
val result = run_probe("sffi_v2_explicit_optional_nil_probe.spl")
step("Confirm explicit absence remains a successful None result")
expect(result.2).to_equal(0)
expect(result.0).to_contain("NONE_OK")
```

</details>

### REQ-SFFI-V2-005/006: unresolved externs fail without fabricated values

#### should reject an unresolved symbol without fabricating a result

- should reject an unresolved symbol without fabricating a result
- Reject a missing or null symbol
- Confirm symbol resolution fails with the canonical diagnostic
- Confirm the failed call did not continue with integer zero
   - Expected: result.0 equals ``
- Confirm diagnostics identify the symbol that failed admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unresolved symbol without fabricating a result")
step("Reject a missing or null symbol")
val result = run_probe("sffi_v2_unresolved_dynamic_extern_probe.spl")
step("Confirm symbol resolution fails with the canonical diagnostic")
expect(result.2).to_be_greater_than(0)
expect(combined_output(result)).to_contain("E-SFFI-001")
step("Confirm the failed call did not continue with integer zero")
expect(result.0).to_equal("")
step("Confirm diagnostics identify the symbol that failed admission")
expect(combined_output(result)).to_contain("sffi_v2_symbol_that_does_not_exist")
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-SFFI-V2-001/002`
- `REQ-SFFI-V2-005/006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12792cd1c15ed169b8432c0319f46930c44a0f436f771ab87b1b952dc33e3248`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12792cd1c15ed169b8432c0319f46930c44a0f436f771ab87b1b952dc33e3248`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12792cd1c15ed169b8432c0319f46930c44a0f436f771ab87b1b952dc33e3248`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl
mirror: doc/06_spec/03_system/compiler/sffi_v2_p0_fail_closed_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/compiler/sffi_v2_p0_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/sffi_v2_p0_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should reject fallthrough from a non-optional text function' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject fallthrough from a non-optional text function' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow a unit function to fall through' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should allow a unit function to fall through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve explicitly returned optional absence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve explicitly returned optional absence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unresolved symbol without fabricating a result' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an unresolved symbol without fabricating a result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
