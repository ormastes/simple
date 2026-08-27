# try_operator_error_propagation_spec

> Verifies the try operator error propagation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# try_operator_error_propagation_spec

Verifies the try operator error propagation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/try_operator_error_propagation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the try operator error propagation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### try operator error propagation

#### propagates Err out of a `val x = f()?` binding

- Verify: propagates Err out of a val x = f()? binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: propagates Err out of a val x = f()? binding")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_bind(true)) to_equal "ERR:boom"
```

</details>

#### still returns Ok on the success path of a binding

- Verify: still returns Ok on the success path of a binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: still returns Ok on the success path of a binding")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_bind(false)) to_equal "OK:bound:payload"
```

</details>

#### early-returns from a bare `f()?` statement with no binding

- Verify: early-returns from a bare f()? statement with no binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: early-returns from a bare f()? statement with no binding")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_stmt(true)) to_equal "ERR:boom"
```

</details>

#### falls through a bare `f()?` statement when Ok

- Verify: falls through a bare f()? statement when Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: falls through a bare f()? statement when Ok")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_stmt(false)) to_equal "OK:fellthrough"
```

</details>

#### does not reinterpret the Err payload as the Ok payload type

- Verify: does not reinterpret the Err payload as the Ok payload type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: does not reinterpret the Err payload as the Ok payload type")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_i64(true)) to_equal "ERR:boom"
```

</details>

#### unwraps a non-text Ok payload correctly

- Verify: unwraps a non-text Ok payload correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-01_UNIT_TRY_OPERATOR_ERROR_P-001
step("Verify: unwraps a non-text Ok payload correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect _tag(_try_i64(false)) to_equal "OK:n=7"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab972cabf315d59a9778bbc6bab55ad03027a7af8383bfe3c753f1709e607e03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab972cabf315d59a9778bbc6bab55ad03027a7af8383bfe3c753f1709e607e03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab972cabf315d59a9778bbc6bab55ad03027a7af8383bfe3c753f1709e607e03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/try_operator_error_propagation_spec.spl
mirror: doc/06_spec/01_unit/try_operator_error_propagation_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/try_operator_error_propagation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/try_operator_error_propagation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/try_operator_error_propagation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
