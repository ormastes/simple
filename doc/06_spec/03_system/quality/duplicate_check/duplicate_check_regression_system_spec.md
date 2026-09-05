# Duplicate Check Regression System Specification

> <details>

<!-- sdn-diagram:id=duplicate_check_regression_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=duplicate_check_regression_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

duplicate_check_regression_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=duplicate_check_regression_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Regression System Specification

## Scenarios

### duplicate-check system regressions

<details>
<summary>Advanced: executes the CLI regression unit spec end-to-end</summary>

#### executes the CLI regression unit spec end-to-end _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _, code) = run_spec("test/unit/app/duplicate_check/duplicate_check_spec.spl")

expect(code).to_equal(0)
expect(stdout).to_contain("Passed:")
expect(stdout).to_contain("All tests passed")
```

</details>


</details>

<details>
<summary>Advanced: executes semantic fallback regressions end-to-end</summary>

#### executes semantic fallback regressions end-to-end _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _, code) = run_spec("test/system/duplicate_check/semantic_fallback_probe_spec.spl")

expect(code).to_equal(0)
expect(stdout).to_contain("Passed:")
expect(stdout).to_contain("All tests passed")
```

</details>


</details>

<details>
<summary>Advanced: runs semantic analysis by default for bare duplicate-check invocations</summary>

#### runs semantic analysis by default for bare duplicate-check invocations _(slow)_

1. make cli fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_check_system_default"
make_cli_fixture(root)

val (stdout, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--semantic-threshold",
    "0.70",
    "--ollama-url",
    "http://127.0.0.1:9"
])

expect(code).to_equal(1)
expect(stdout).to_contain("Source: 2 items, 2 documented")
expect(stdout).to_contain("Summary: 2 total, 2 documented")
expect(stdout).to_contain("[text-based fallback]")
```

</details>


</details>

<details>
<summary>Advanced: runs token mode for 5-line code duplication</summary>

#### runs token mode for 5-line code duplication _(slow)_

1. make token fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_check_system_token"
make_token_fixture(root)

val (_, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--mode",
    "token",
    "--min-lines",
    "5",
    "--min-tokens",
    "8"
])

expect(code).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: runs cosine mode for fuzzy duplication</summary>

#### runs cosine mode for fuzzy duplication _(slow)_

1. make cosine fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_check_system_cosine"
make_cosine_fixture(root)

val (_, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--mode",
    "cosine",
    "--min-lines",
    "5",
    "--min-tokens",
    "8",
    "--similarity-threshold",
    "0.55"
])

expect(code).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: falls back cleanly in bootstrap semantic mode without HTTP extern support</summary>

#### falls back cleanly in bootstrap semantic mode without HTTP extern support _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, _, code) = run_bootstrap([
    "run",
    "src/compiler/90.tools/duplicate_check/main.spl",
    "src/compiler/90.tools/duplicate_check",
    "--semantic",
    "--semantic-threshold",
    "0.7",
    "--ollama-url",
    "http://127.0.0.1:9"
])

expect(code).to_equal(0)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- duplicate-check system regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
