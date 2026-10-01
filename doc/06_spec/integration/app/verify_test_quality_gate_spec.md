# Verify Test Quality Gate Specification

> Tests covering anti-dummy / anti-stub verify gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verify Test Quality Gate Specification

## Scenarios

### anti-dummy / anti-stub verify gate

#### fails on tautological test assertions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails on tautological test assertions
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on tautological test assertions")
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "bad_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        expect(true).to_equal(true)\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on placeholder pass helper in tests

- fails on placeholder pass helper in tests
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on placeholder pass helper in tests")
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "pass_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        pass_todo\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on print based skip placeholders in tests

- fails on print based skip placeholders in tests
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on print based skip placeholders in tests")
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "print_skip_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        print \"[skip] env unavailable\"\n" +
    "        return\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on examples with no real assertion

- fails on examples with no real assertion
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on examples with no real assertion")
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "empty_example_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        run_check()\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on boolean-wrapper assertions in tests

- fails on boolean-wrapper assertions in tests
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on boolean-wrapper assertions in tests")
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "wrapped_bool_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        expect(code != 0).to_equal(true)\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on obvious stub implementations in source

- fails on obvious stub implementations in source
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on obvious stub implementations in source")
val path = write_fixture(TEST_QUALITY_SOURCE_FIXTURES,
    "stub_impl.spl",
    "fn answer(x: i64) -> i64:\n" +
    "    0\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on explicit production placeholders in source

- fails on explicit production placeholders in source
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on explicit production placeholders in source")
val path = write_fixture(TEST_QUALITY_SOURCE_FIXTURES,
    "placeholder_impl.spl",
    "fn answer(x: i64) -> i64:\n" +
    "    pass_todo(\"implement answer\")\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### fails on local suppression of placeholder quality lints

- fails on local suppression of placeholder quality lints
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on local suppression of placeholder quality lints")
val suppression = "@" + "allow(spipe_placeholder_tests)\n"
val path = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "suppressed_spec.spl",
    suppression +
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        expect(true).to_equal(true)\n")
val report = build_test_quality_verify_report("fixture", [path], false)
expect(report.status).to_equal("FAIL")
```

</details>

#### warns on registered visible debt markers

- warns on registered visible debt markers
   - Expected: report.status equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("warns on registered visible debt markers")
val report = build_test_quality_verify_report(
    "fixture",
    ["test/integration/app/verify_test_quality_gate_spec.spl"],
    false
)
val rendered = render_test_quality_verify_report(report)
expect(report.status).to_equal("WARN")
expect(report.warnings).to_be_greater_than(0)
expect(rendered).to_contain("[WARN]")
expect(rendered).to_contain("registered visible debt marker")
```

</details>

#### passes on clean test and source fixtures

- passes on clean test and source fixtures
   - Expected: report.status equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("passes on clean test and source fixtures")
val good_test = write_fixture(TEST_QUALITY_TEST_FIXTURES,
    "good_spec.spl",
    "describe \"x\":\n" +
    "    it \"y\":\n" +
    "        expect(1 + 1).to_equal(2)\n")
val good_src = write_fixture(TEST_QUALITY_SOURCE_FIXTURES,
    "good_src.spl",
    "fn identity(x: i64) -> i64:\n" +
    "    x\n")
val report = build_test_quality_verify_report("fixture", [good_test, good_src], false)
expect(report.status).to_equal("PASS")
expect(render_test_quality_verify_report(report)).to_contain("STATUS: PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/verify_test_quality_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering anti-dummy / anti-stub verify gate.
- anti-dummy / anti-stub verify gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48ba1ba29feaa1d70df72dc5851c89968a9f92468d752b0c335b98347bb0d418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48ba1ba29feaa1d70df72dc5851c89968a9f92468d752b0c335b98347bb0d418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48ba1ba29feaa1d70df72dc5851c89968a9f92468d752b0c335b98347bb0d418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/verify_test_quality_gate_spec.spl
mirror: doc/06_spec/integration/app/verify_test_quality_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/verify_test_quality_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/verify_test_quality_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/verify_test_quality_gate_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on tautological test assertions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/verify_test_quality_gate_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on placeholder pass helper in tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/verify_test_quality_gate_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on print based skip placeholders in tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
