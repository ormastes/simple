# Compile Log Modes Specification

> <details>

<!-- sdn-diagram:id=compile_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Log Modes Specification

## Scenarios

### compile log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_compile(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Usage: simple compile")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for missing source output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_compile(["--log-mode=json"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"compile\"")
expect(out).to_contain("\"error\":\"compile requires a source file\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_compile(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Usage: simple compile")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_compile(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### delegates compile option queries to the rust CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_compile(["--list-optimizations"])
expect(code).to_equal(0)
expect(out).to_contain("Simple optimization guide")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/compile_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compile log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
