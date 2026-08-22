# fixture_spec

> Verifies the fixture behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fixture_spec

Verifies the fixture behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/fixture_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the fixture behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Fixture Tests

### using test data

#### tests with fixture value

- Verify: tests with fixture value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_FIXTURE-001
step("Verify: tests with fixture value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fixture_value = 42
expect fixture_value == 42
```

</details>

#### tests with fixture string

- Verify: tests with fixture string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_FIXTURE-001
step("Verify: tests with fixture string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fixture_name = "test_user"
expect fixture_name == "test_user"
```

</details>

#### tests with fixture list

- Verify: tests with fixture list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_FIXTURE-001
step("Verify: tests with fixture list")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fixture_list = [1, 2, 3]
expect fixture_list[0] == 1
expect fixture_list[1] == 2
expect fixture_list[2] == 3
```

</details>

### computed fixtures

#### uses computed test data

- Verify: uses computed test data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_FIXTURE-001
step("Verify: uses computed test data")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val base = 10
val multiplier = 5
val expected = base * multiplier
expect expected == 50
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22578aa822d1f1be3560954f4ce80d5343f70e64de444a3d621cf9b3cc47c162`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22578aa822d1f1be3560954f4ce80d5343f70e64de444a3d621cf9b3cc47c162`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22578aa822d1f1be3560954f4ce80d5343f70e64de444a3d621cf9b3cc47c162`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/fixture_spec.spl
mirror: doc/06_spec/01_unit/std/fixture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/fixture_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/fixture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/fixture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
