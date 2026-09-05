# Query Log Modes Specification

> <details>

<!-- sdn-diagram:id=query_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Log Modes Specification

## Scenarios

### query log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for usage output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"query\"")
expect(out).to_contain("\"status\":\"usage\"")
```

</details>

#### supports log-mode json for missing path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["needle", "/tmp/simple-query-missing-path", "--log-mode=json"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"query\"")
expect(out).to_contain("\"error\":\"path not found\"")
```

</details>

#### supports dot progress for missing path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["needle", "/tmp/simple-query-missing-path", "--progress=dot"])
expect(code).to_equal(1)
expect(out).to_start_with(".")
```

</details>

#### keeps command-specific count option

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["zz-no-match", "src/app/query", "--count"])
expect(code).to_equal(0)
expect(out.trim()).to_equal("0")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_query(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/query_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
