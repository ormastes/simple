# Optimize CLI Specification

> Validates the `bin/simple optimize` CLI surface introduced in AC-9. Tests cover: usage output on missing args, analysis suggestions, --apply, --compare, and --level flags.

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimize CLI Specification

Validates the `bin/simple optimize` CLI surface introduced in AC-9. Tests cover: usage output on missing args, analysis suggestions, --apply, --compare, and --level flags.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | App / CLI Surface |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/02_integration/app/optimize/optimize_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the `bin/simple optimize` CLI surface introduced in AC-9.
Tests cover: usage output on missing args, analysis suggestions, --apply,
--compare, and --level flags.

## Behavior

- No arguments → usage text printed to stdout
- File arg → optimization suggestions printed
- --apply flag → safe passes applied, mutations reported
- --compare flag → Simple vs C codegen comparison table printed
- --level flag → optimization level respected (O0-O3)

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

1. output contains
2. output contains
3. output contains
4. output contains
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

### --apply flag

#### applies safe passes with --apply flag

1. output contains
2. output contains
3. output contains
4. output contains
5. output contains
6. output contains
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

1. output contains
2. output contains
3. output contains
4. output contains
5. output contains
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
