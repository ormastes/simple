# Integration Specification

> Tests covering ExpectedResult, TestSource, TestAssertion, IntegrationTestResult, IntegrationTest, IntegrationTestSuite, IntegrationSuiteResult, Convenience Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Specification

## Scenarios

### ExpectedResult

#### creates success expectation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates success expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates success expectation")
# ExpectedResult.Success.to_text() == "success"
pass
```

</details>

#### creates compile error expectation

- creates compile error expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates compile error expectation")
# ExpectedResult.CompileError("msg").to_text() contains "compile_error"
pass
```

</details>

#### creates runtime error expectation

- creates runtime error expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates runtime error expectation")
# ExpectedResult.RuntimeError("msg").to_text() contains "runtime_error"
pass
```

</details>

#### creates any error expectation

- creates any error expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates any error expectation")
# ExpectedResult.AnyError.to_text() == "any_error"
pass
```

</details>

### TestSource

#### creates source with name

- creates source with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source with name")
# TestSource.create("foo.spl", "code").name == "foo.spl"
pass
```

</details>

#### identifies main file

- identifies main file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies main file")
# TestSource.main_file("code").is_main == true
pass
```

</details>

#### non-main file not marked as main

- non-main file not marked as main


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-main file not marked as main")
# TestSource.create("helper.spl", "code").is_main == false
pass
```

</details>

### TestAssertion

#### creates output contains assertion

- creates output contains assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates output contains assertion")
# TestAssertion.OutputContains("hello").to_text() contains "hello"
pass
```

</details>

#### creates output equals assertion

- creates output equals assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates output equals assertion")
# TestAssertion.OutputEquals("hello").to_text() contains "output_equals"
pass
```

</details>

#### creates exit code assertion

- creates exit code assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates exit code assertion")
# TestAssertion.ExitCode(0).to_text() == "exit_code(0)"
pass
```

</details>

#### creates compile time assertion

- creates compile time assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates compile time assertion")
# TestAssertion.CompileTime(1000).to_text() contains "1000"
pass
```

</details>

#### creates no warnings assertion

- creates no warnings assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates no warnings assertion")
# TestAssertion.NoWarnings.to_text() == "no_warnings"
pass
```

</details>

### IntegrationTestResult

#### creates success result

- creates success result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates success result")
# IntegrationTestResult.success("test", 100, 50, "output")
# result.passed == true
pass
```

</details>

#### creates compile failure result

- creates compile failure result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates compile failure result")
# IntegrationTestResult.compile_failure("test", 100, "error")
# result.passed == false
# result.compile_success == false
pass
```

</details>

#### formats result with status

- formats result with status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats result with status")
# result.format_result() contains "PASS" or "FAIL"
pass
```

</details>

#### formats failed assertions

- formats failed assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats failed assertions")
# result with failed_assertions
# format_result() contains assertion messages
pass
```

</details>

### IntegrationTest

#### creates test with name

- creates test with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test with name")
# IntegrationTest.create("my_test").name == "my_test"
pass
```

</details>

#### adds source files

- adds source files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds source files")
# test.add_source("foo.spl", "code")
# test.sources.len() == 1
pass
```

</details>

#### sets main source

- sets main source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets main source")
# test.main_source("code")
# test.sources[0].is_main == true
pass
```

</details>

#### sets expectations

- sets expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets expectations")
# test.expect_success()
# test.expected == ExpectedResult.Success
pass
```

</details>

#### adds output assertion

- adds output assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds output assertion")
# test.expect_output("hello")
# test.assertions contains OutputEquals
pass
```

</details>

#### adds environment variable

- adds environment variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds environment variable")
# test.with_env("KEY", "VALUE")
# test.env_vars["KEY"] == "VALUE"
pass
```

</details>

#### sets timeout

- sets timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets timeout")
# test.with_timeout(5000)
# test.timeout_ms == 5000
pass
```

</details>

### IntegrationTestSuite

#### creates suite with name

- creates suite with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates suite with name")
# IntegrationTestSuite.create("my_suite").name == "my_suite"
pass
```

</details>

#### adds tests

- adds tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds tests")
# suite.add_test(test)
# suite.tests.len() == 1
pass
```

</details>

#### runs all tests

- runs all tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs all tests")
# suite.run_all() returns IntegrationSuiteResult
pass
```

</details>

### IntegrationSuiteResult

#### counts passed tests

- counts passed tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts passed tests")
# result.total_passed reflects actual passed count
pass
```

</details>

#### counts failed tests

- counts failed tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts failed tests")
# result.total_failed reflects actual failed count
pass
```

</details>

#### formats summary

- formats summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats summary")
# result.format_summary() contains suite name and counts
pass
```

</details>

### Convenience Functions

#### creates quick test

- creates quick test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates quick test")
# quick_test("name", "code")
# test.expected == ExpectedResult.Success
pass
```

</details>

#### creates error test

- creates error test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error test")
# error_test("name", "code", "error")
# test.expected is CompileError
pass
```

</details>

#### creates output test

- creates output test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates output test")
# output_test("name", "code", "output")
# test has OutputEquals assertion
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner/integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ExpectedResult, TestSource, TestAssertion, IntegrationTestResult, IntegrationTest, IntegrationTestSuite, IntegrationSuiteResult, Convenience Functions.
- ExpectedResult
- TestSource
- TestAssertion
- IntegrationTestResult
- IntegrationTest
- IntegrationTestSuite
- IntegrationSuiteResult
- Convenience Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `9727d4656c55d57488189f285c7fd5b83ef785d0a274145780134cb3cc00b42e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9727d4656c55d57488189f285c7fd5b83ef785d0a274145780134cb3cc00b42e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9727d4656c55d57488189f285c7fd5b83ef785d0a274145780134cb3cc00b42e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/test_runner/integration_spec.spl
mirror: doc/06_spec/unit/app/test_runner/integration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/app/test_runner/integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner/integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner/integration_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/app/test_runner/integration_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates success expectation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/integration_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates compile error expectation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/integration_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates runtime error expectation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
