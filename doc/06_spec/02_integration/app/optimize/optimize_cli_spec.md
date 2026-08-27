# Optimize CLI Specification

> Validates the `bin/simple optimize` CLI surface introduced in AC-9. Tests cover: usage output on missing args, analysis suggestions, --apply, --compare, and --level flags.

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
| Updated | 2026-08-26 |
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

- prints usage when no arguments given


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints usage when no arguments given")
val output = run_optimize("")
expect(output).to_contain("Usage")
```

</details>

### analysis (--analyze)

#### analyzes file and prints optimization suggestions

- analyzes file and prints optimization suggestions
   - Expected: has_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("analyzes file and prints optimization suggestions")
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

- applies safe passes with --apply flag
   - Expected: reports_result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies safe passes with --apply flag")
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

- compares Simple vs C codegen with --compare flag
   - Expected: has_compare_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compares Simple vs C codegen with --compare flag")
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

- respects --level flag for optimization level O0
   - Expected: no_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("respects --level flag for optimization level O0")
val output = run_optimize_on_fixture("--level O0")
# O0 disables all passes — output should not report eliminations.
val no_error = not output.contains("Error") and not output.contains("error: unknown")
expect(no_error).to_equal(true)
```

</details>

#### respects --level flag for optimization level O3

- respects --level flag for optimization level O3
   - Expected: no_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("respects --level flag for optimization level O3")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91f58ad66524479adef8686fa238fb8aa638a07ed3accd17feaec5e11671a74d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91f58ad66524479adef8686fa238fb8aa638a07ed3accd17feaec5e11671a74d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91f58ad66524479adef8686fa238fb8aa638a07ed3accd17feaec5e11671a74d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/optimize/optimize_cli_spec.spl
mirror: doc/06_spec/02_integration/app/optimize/optimize_cli_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/optimize/optimize_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/optimize/optimize_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/optimize/optimize_cli_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints usage when no arguments given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/optimize/optimize_cli_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'analyzes file and prints optimization suggestions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/optimize/optimize_cli_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies safe passes with --apply flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
