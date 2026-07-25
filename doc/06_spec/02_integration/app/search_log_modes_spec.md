# Search Log Modes Specification

> <details>

<!-- sdn-diagram:id=search_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=search_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

search_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=search_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Search Log Modes Specification

## Scenarios

### search log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_search(["run", "src/app/search/main.spl", "--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_search(["run", "src/app/search/main.spl", "zz-no-match", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"query\":\"zz-no-match\"")
expect(out).to_contain("\"count\":0")
expect(out).to_contain("\"results\":[]")
```

</details>

#### supports dot progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_search(["run", "src/app/search/main.spl", "zz-no-match", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_search(["run", "src/app/search/main.spl", "zz-no-match", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/search_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- search log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
