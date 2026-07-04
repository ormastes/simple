# Code Quality Tools

> Tests the code quality tooling pipeline including linting, formatting, and static analysis checks. Verifies that quality tools correctly detect issues, report diagnostics, and apply automated fixes to Simple source files.

<!-- sdn-diagram:id=code_quality_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=code_quality_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

code_quality_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=code_quality_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Code Quality Tools

Tests the code quality tooling pipeline including linting, formatting, and static analysis checks. Verifies that quality tools correctly detect issues, report diagnostics, and apply automated fixes to Simple source files.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/code_quality_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the code quality tooling pipeline including linting, formatting, and static
analysis checks. Verifies that quality tools correctly detect issues, report
diagnostics, and apply automated fixes to Simple source files.

## Scenarios

### Code Quality Tools

#### prints lint usage when no files are provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = run_quality_tool(["lint"])
expect(code).to_equal(1)
expect(out).to_contain("Usage: simple lint")
expect(out).to_contain("Runs lint passes")
```

</details>

#### reports clean files through the lightweight lint entrypoint

1. write quality fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
write_quality_fixture(CLEAN_FIXTURE, "fn main() -> i64:\n    0\n")
val (out, err, code) = run_quality_tool(["lint", CLEAN_FIXTURE])
expect(code).to_equal(0)
expect(out).to_contain("lint: " + CLEAN_FIXTURE + " OK")
expect(out).to_contain("Lint passed: all files clean")
```

</details>

#### prints formatter usage when no files are provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = run_quality_tool(["fmt"])
expect(code).to_equal(1)
expect(out).to_contain("Usage: simple fmt")
expect(out).to_contain("--check")
```

</details>

#### rejects unknown quality commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = run_quality_tool(["unknown"])
expect(code).to_equal(1)
expect(out).to_contain("Unknown command: unknown")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
