# `simple run` diagnostic contract

> Exercises the real interpreted run path for runtime-facing diagnostics so stable

<!-- sdn-diagram:id=run_diagnostics_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=run_diagnostics_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

run_diagnostics_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=run_diagnostics_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `simple run` diagnostic contract

Exercises the real interpreted run path for runtime-facing diagnostics so stable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the real interpreted run path for runtime-facing diagnostics so stable
codes and help text are not lost in process-level error rendering.

## Scenarios

### `simple run` diagnostics

#### prints stable undefined function code and help

1. seed undefined function source
   - Expected: code equals `1`
   - Expected: combined does not contain `semantic:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_undefined_function_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", UNDEFINED_FUNCTION_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E1002]")
expect(combined).to_contain("function `missing_function` not found")
expect(combined).to_contain("= help: check the function name or import the module that defines it")
expect(combined.contains("semantic:")).to_equal(false)
```

</details>

#### prints stable division by zero code and help

1. seed division by zero source
   - Expected: code equals `1`
   - Expected: combined does not contain `semantic:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_division_by_zero_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", DIVISION_BY_ZERO_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E2001]")
expect(combined).to_contain("division by zero")
expect(combined).to_contain("= help: check the divisor before dividing")
expect(combined.contains("semantic:")).to_equal(false)
```

</details>

#### prints stable missing file code and help

1. remove missing run fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_missing_run_fixture()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", MISSING_RUN_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E0001]")
expect(combined).to_contain("cannot read file")
expect(combined).to_contain("= help: check that the path exists and is readable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
