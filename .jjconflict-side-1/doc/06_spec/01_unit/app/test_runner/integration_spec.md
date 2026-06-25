# Integration Specification

> <details>

<!-- sdn-diagram:id=integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Specification

## Scenarios

### ExpectedResult

#### creates success expectation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ExpectedResult.Success.to_text() == "success"
pass
```

</details>

#### creates compile error expectation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ExpectedResult.CompileError("msg").to_text() contains "compile_error"
pass
```

</details>

#### creates runtime error expectation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ExpectedResult.RuntimeError("msg").to_text() contains "runtime_error"
pass
```

</details>

#### creates any error expectation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ExpectedResult.AnyError.to_text() == "any_error"
pass
```

</details>

### TestSource

#### creates source with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestSource.create("foo.spl", "code").name == "foo.spl"
pass
```

</details>

#### identifies main file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestSource.main_file("code").is_main == true
pass
```

</details>

#### non-main file not marked as main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestSource.create("helper.spl", "code").is_main == false
pass
```

</details>

### TestAssertion

#### creates output contains assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestAssertion.OutputContains("hello").to_text() contains "hello"
pass
```

</details>

#### creates output equals assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestAssertion.OutputEquals("hello").to_text() contains "output_equals"
pass
```

</details>

#### creates exit code assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestAssertion.ExitCode(0).to_text() == "exit_code(0)"
pass
```

</details>

#### creates compile time assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestAssertion.CompileTime(1000).to_text() contains "1000"
pass
```

</details>

#### creates no warnings assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestAssertion.NoWarnings.to_text() == "no_warnings"
pass
```

</details>

### IntegrationTestResult

#### creates success result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntegrationTestResult.success("test", 100, 50, "output")
# result.passed == true
pass
```

</details>

#### creates compile failure result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntegrationTestResult.compile_failure("test", 100, "error")
# result.passed == false
# result.compile_success == false
pass
```

</details>

#### formats result with status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_result() contains "PASS" or "FAIL"
pass
```

</details>

#### formats failed assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result with failed_assertions
# format_result() contains assertion messages
pass
```

</details>

### IntegrationTest

#### creates test with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntegrationTest.create("my_test").name == "my_test"
pass
```

</details>

#### adds source files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.add_source("foo.spl", "code")
# test.sources.len() == 1
pass
```

</details>

#### sets main source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.main_source("code")
# test.sources[0].is_main == true
pass
```

</details>

#### sets expectations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.expect_success()
# test.expected == ExpectedResult.Success
pass
```

</details>

#### adds output assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.expect_output("hello")
# test.assertions contains OutputEquals
pass
```

</details>

#### adds environment variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.with_env("KEY", "VALUE")
# test.env_vars["KEY"] == "VALUE"
pass
```

</details>

#### sets timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.with_timeout(5000)
# test.timeout_ms == 5000
pass
```

</details>

### IntegrationTestSuite

#### creates suite with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntegrationTestSuite.create("my_suite").name == "my_suite"
pass
```

</details>

#### adds tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suite.add_test(test)
# suite.tests.len() == 1
pass
```

</details>

#### runs all tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suite.run_all() returns IntegrationSuiteResult
pass
```

</details>

### IntegrationSuiteResult

#### counts passed tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.total_passed reflects actual passed count
pass
```

</details>

#### counts failed tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.total_failed reflects actual failed count
pass
```

</details>

#### formats summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_summary() contains suite name and counts
pass
```

</details>

### Convenience Functions

#### creates quick test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# quick_test("name", "code")
# test.expected == ExpectedResult.Success
pass
```

</details>

#### creates error test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# error_test("name", "code", "error")
# test.expected is CompileError
pass
```

</details>

#### creates output test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/test_runner/integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
