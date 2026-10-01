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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runner Specification

## Scenarios

### Test Runner Integration

#### keeps test runner result and option types available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_test_runner_source("src/app/test_runner_new/test_runner_types.spl")

expect(source).to_contain("struct TestOptions")
expect(source).to_contain("struct TestFileResult")
expect(source).to_contain("struct TestRunResult")
```

</details>

#### keeps interpreter and native execution entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_test_runner_source("src/app/test_runner_new/test_runner_execute.spl")

expect(source).to_contain("fn run_test_file_interpreter(file_path: text, options: TestOptions) -> TestFileResult")
expect(source).to_contain("fn run_test_file_native(file_path: text, options: TestOptions) -> TestFileResult")
```

</details>

#### keeps top-level run_tests entrypoint available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_test_runner_source("src/app/test_runner_new/test_runner_main.spl")

expect(source).to_contain("fn run_tests(options: TestOptions) -> TestRunResult")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/spec/runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Runner Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
