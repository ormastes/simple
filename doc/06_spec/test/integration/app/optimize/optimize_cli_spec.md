# Optimize CLI Specification

> Validates the `bin/simple optimize` CLI surface introduced in AC-9. The optimizer is often run by agents on large `.spl` files during SPipe verification. Its default output must therefore stay bounded and scannable. Detailed per-location opportunity output is still available, but it is an explicit opt-in mode.

<!-- sdn-diagram:id=optimize_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimize_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimize_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimize_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimize CLI Specification

Validates the `bin/simple optimize` CLI surface introduced in AC-9. The optimizer is often run by agents on large `.spl` files during SPipe verification. Its default output must therefore stay bounded and scannable. Detailed per-location opportunity output is still available, but it is an explicit opt-in mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | App / CLI Surface |
| Difficulty | 2/5 |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/integration/app/optimize/optimize_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the `bin/simple optimize` CLI surface introduced in AC-9.
The optimizer is often run by agents on large `.spl` files during SPipe
verification. Its default output must therefore stay bounded and scannable.
Detailed per-location opportunity output is still available, but it is an
explicit opt-in mode.

This spec covers:

- usage output on missing args
- analysis suggestions for a real fixture
- concise default opportunity reporting
- verbose per-location opportunity reporting
- --apply behavior
- --compare behavior
- --level parsing for O0 and O3

## Syntax

The direct optimizer entrypoint is:

```bash
bin/simple src/app/optimize/main.spl optimize FILE [FLAGS]
```

The wrapper form may expose the same surface as:

```bash
bin/simple optimize FILE [FLAGS]
```

Supported analysis flags covered here:

```bash
--full
--level=O0
--level=O3
--verbose
--apply
--compare
```

## Examples

Default bounded analysis:

```bash
bin/simple src/app/optimize/main.spl optimize test/fixtures/optimize/simple_loop.spl --full --level=O3
```

Expected operator signal:

- output includes `By pass (use --verbose for per-location detail):`
- output lists one row per opportunity class with an `xN` count
- output does not print repeated `@ line` rows

Verbose diagnostic analysis:

```bash
bin/simple src/app/optimize/main.spl optimize test/fixtures/optimize/simple_loop.spl --full --level=O3 --verbose
```

Expected operator signal:

- output includes individual opportunity locations
- output includes `@ line`
- output is intentionally larger and should be used only when detail is needed

## Resource Safety Contract

The default optimizer report is used in long-running SPipe lanes. It must not
flood the agent context with thousands of repeated opportunity rows.

The CLI keeps this contract by aggregating opportunities by:

- domain
- expected speedup
- pass name

The verbose mode keeps the original per-location behavior for human debugging.
This preserves diagnostic usefulness without making the default verification
path expensive.

## Behavior Matrix

| Scenario | Required evidence |
|----------|-------------------|
| no arguments | usage text is printed |
| default analysis | at least one optimization section is visible |
| default full analysis | aggregate `By pass` section is visible |
| default full analysis | no per-location `@ line` rows are printed |
| verbose full analysis | per-location `@ line` rows are printed |
| apply | command reports applied or no-op optimization result |
| compare | command reports comparison data or unavailable state |
| O0 | level flag parses without unknown-flag error |
| O3 | level flag parses without unknown-flag error |

## Failure Modes

The spec intentionally fails if:

- default output regresses to repeated per-location rows
- verbose mode no longer exposes per-location detail
- level parsing treats the documented flags as unknown
- the fixture no longer produces any optimizer signal

Compiler or import-graph diagnostics printed before `main()` runs are tracked
separately. This spec is scoped to optimizer CLI stdout contract after the app
entrypoint starts.

## Behavior

- No arguments -> usage text printed to stdout
- File arg -> optimization suggestions printed
- Default full analysis -> concise grouped counts
- --verbose -> per-location opportunity rows
- --apply flag -> safe passes applied, mutations reported
- --compare flag -> Simple vs C codegen comparison table printed
- --level flag -> optimization level respected (O0-O3)

## Scenarios

### optimize CLI

### usage

#### prints usage when no arguments given

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize("")
expect(output).to_contain("Usage")
```

</details>

### analysis (--analyze)

#### analyzes file and prints optimization suggestions

- output contains
- output contains
- output contains
- output contains
   - Expected: has_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("")
# Expect at least one suggestion section header.
val has_output = (
    output.contains("suggestion") or
    output.contains("Suggestion") or
    output.contains("optimization") or
    output.contains("Optimization")
)
expect(has_output).to_equal(true)
```

</details>

#### defaults to concise per-pass opportunity counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--full --level O3")
expect(output).to_contain("By pass (use --verbose for per-location detail):")
expect(output.contains("@ line")).to_equal(false)
```

</details>

#### prints per-location opportunity detail with --verbose

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--full --level O3 --verbose")
expect(output.contains("By pass (use --verbose for per-location detail):")).to_equal(false)
expect(output).to_contain("@ line")
```

</details>

### --apply flag

#### applies safe passes with --apply flag

- output contains
- output contains
- output contains
- output contains
- output contains
- output contains
   - Expected: reports_result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--apply")
# After applying passes the CLI reports what was changed or
# confirms no mutations if the fixture has nothing to optimize.
val reports_result = (
    output.contains("applied") or
    output.contains("Applied") or
    output.contains("eliminated") or
    output.contains("hoisted") or
    output.contains("promoted") or
    output.contains("No optimizations")
)
expect(reports_result).to_equal(true)
```

</details>

### --compare flag

#### compares Simple vs C codegen with --compare flag

- output contains
- output contains
- output contains
- output contains
- output contains
   - Expected: has_compare_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--compare")
# Comparison report contains either a table separator or the
# word "Simple" / "C" column header.
val has_compare_output = (
    output.contains("Simple") or
    output.contains("clang") or
    output.contains("compare") or
    output.contains("Compare") or
    output.contains("unavailable")
)
expect(has_compare_output).to_equal(true)
```

</details>

### --level flag

#### respects --level flag for optimization level O0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--level O0")
# O0 disables all passes — output should not report eliminations.
val no_error = not output.contains("Error") and not output.contains("error: unknown")
expect(no_error).to_equal(true)
```

</details>

#### respects --level flag for optimization level O3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = run_optimize_on_fixture("--level O3")
val no_error = not output.contains("error: unknown flag")
expect(no_error).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
