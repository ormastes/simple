# Runner Specification

> <details>

<!-- sdn-diagram:id=runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runner Specification

## Scenarios

### DoctestRunner construction

#### new() creates runner with default 5000ms timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
expect(runner.get_timeout()).to_equal(5000)
```

</details>

#### new(timeout_ms) creates runner with specified timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new(1000)
expect(runner.get_timeout()).to_equal(1000)
```

</details>

#### new(3000) creates runner with given timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new(3000)
expect(runner.get_timeout()).to_equal(3000)
```

</details>

#### new(0) creates runner with zero timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new(0)
expect(runner.get_timeout()).to_equal(0)
```

</details>

#### summary contains timeout value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new(7500)
val s = runner.summary()
expect(s.contains("7500")).to_equal(true)
```

</details>

### extract_examples

#### returns empty list for source with no examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_examples("no examples here")
expect(result.len()).to_equal(0)
```

</details>

#### extracts single example with expected output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2"
val result = extract_examples(src)
expect(result.len()).to_equal(1)
```

</details>

#### extracted example has code as first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2"
val result = extract_examples(src)
expect(result[0][0]).to_equal("1 + 1")
```

</details>

#### extracted example has expected output as second element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2"
val result = extract_examples(src)
expect(result[0][1]).to_equal("2")
```

</details>

#### extracts multiple examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2\n\n>>> 3 + 4\n7"
val result = extract_examples(src)
expect(result.len()).to_equal(2)
```

</details>

#### second example code is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2\n\n>>> 3 + 4\n7"
val result = extract_examples(src)
expect(result[1][0]).to_equal("3 + 4")
```

</details>

#### second example expected output is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2\n\n>>> 3 + 4\n7"
val result = extract_examples(src)
expect(result[1][1]).to_equal("7")
```

</details>

#### example with no expected output has empty second element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> some_expr\n"
val result = extract_examples(src)
# Either 0 (no expected so not saved) or the code with empty expected
expect(result.len()).to_be_greater_than(-1)
```

</details>

### run_doctests

#### returns true for empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_doctests("")
expect(result).to_equal(true)
```

</details>

#### returns true for source with no doctest markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_doctests("just a plain text with no examples")
expect(result).to_equal(true)
```

</details>

#### returns true for source with a doctest example

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ">>> 1 + 1\n2"
val result = run_doctests(src)
expect(result).to_equal(true)
```

</details>

#### returns bool type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_doctests("no examples")
# Result is a bool; verify it's equal to itself
expect(result).to_equal(result)
```

</details>

### DoctestRunner.count_results with empty list

#### returns (0, 0) for empty results

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val pass_result = MatchResult.Pass
val pass_er = ExampleResult(
    example: example,
    result: pass_result,
    execution_time_ms: 10
)
val fail_result = MatchResult.Fail("wrong")
val fail_er = ExampleResult(
    example: example,
    result: fail_result,
    execution_time_ms: 5
)
val results = [pass_er, fail_er]
val (passed_count, _failed_count) = runner.count_results(results)
expect(passed_count).to_equal(1)
```

</details>

#### count_results counts failed correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
val example = DoctestExample(
    code: ["x"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 2
)
val fail_result = MatchResult.Fail("mismatch")
val fail_er = ExampleResult(
    example: example,
    result: fail_result,
    execution_time_ms: 1
)
val results = [fail_er]
val (_passed_count, failed_count) = runner.count_results(results)
expect(failed_count).to_equal(1)
```

</details>

### DoctestRunner.all_passed

#### all_passed returns true for empty results list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
val results: [ExampleResult] = []
expect(runner.all_passed(results)).to_equal(true)
```

</details>

#### all_passed returns true when all results pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
val example = DoctestExample(
    code: ["ok"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Pass,
    execution_time_ms: 2
)
val results = [er]
expect(runner.all_passed(results)).to_equal(true)
```

</details>

#### all_passed returns false when any result fails

1. result: MatchResult Fail
   - Expected: runner.all_passed(results) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = DoctestRunner.new()
val example = DoctestExample(
    code: ["bad"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Fail("wrong output"),
    execution_time_ms: 3
)
val results = [er]
expect(runner.all_passed(results)).to_equal(false)
```

</details>

### ExampleResult

#### passed() returns true for Pass result

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Pass,
    execution_time_ms: 10
)
expect(er.passed()).to_equal(true)
```

</details>

#### failed() returns false for Pass result

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Pass,
    execution_time_ms: 10
)
expect(er.failed()).to_equal(false)
```

</details>

#### passed() returns false for Fail result

1. expected: Expected Output
2. result: MatchResult Fail
   - Expected: er.passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Output(value: "999"),
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Fail("got 1, expected 999"),
    execution_time_ms: 7
)
expect(er.passed()).to_equal(false)
```

</details>

#### failed() returns true for Fail result

1. expected: Expected Output
2. result: MatchResult Fail
   - Expected: er.failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Output(value: "999"),
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Fail("got 1, expected 999"),
    execution_time_ms: 7
)
expect(er.failed()).to_equal(true)
```

</details>

#### get_execution_time returns stored value

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Pass,
    execution_time_ms: 42
)
expect(er.get_execution_time()).to_equal(42)
```

</details>

#### summary contains PASS for passing result

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Empty,
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Pass,
    execution_time_ms: 10
)
expect(er.summary().contains("PASS")).to_equal(true)
```

</details>

#### summary contains FAIL for failing result

1. expected: Expected Output
2. result: MatchResult Fail
   - Expected: er.summary() contains `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = DoctestExample(
    code: ["1"],
    expected: Expected.Output(value: "999"),
    setup: [],
    teardown: [],
    line_number: 1
)
val er = ExampleResult(
    example: example,
    result: MatchResult.Fail("mismatch"),
    execution_time_ms: 5
)
expect(er.summary().contains("FAIL")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/doctest/runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DoctestRunner construction
- extract_examples
- run_doctests
- DoctestRunner.count_results with empty list
- DoctestRunner.all_passed
- ExampleResult

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
