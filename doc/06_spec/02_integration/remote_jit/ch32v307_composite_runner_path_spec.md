# CH32V307 Composite Runner Path Regression

> Verifies that the CH32V307 composite runner no longer short-circuits through the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))` through the real adapter-backed execution flow.

<!-- sdn-diagram:id=ch32v307_composite_runner_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ch32v307_composite_runner_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ch32v307_composite_runner_path_spec -> app
ch32v307_composite_runner_path_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ch32v307_composite_runner_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Composite Runner Path Regression

Verifies that the CH32V307 composite runner no longer short-circuits through the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))` through the real adapter-backed execution flow.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-013 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | N/A |
| Source | `test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the CH32V307 composite runner no longer short-circuits through
the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))`
through the real adapter-backed execution flow.

This spec is intentionally host-aware:

- if `wlink` or the probe is unavailable, the runner must skip cleanly
- if hardware is available, the composite runner must take the real CH32
  adapter path
- the result must not regress to the old "not implemented" message

This file is the authoritative regression for composite-runner wiring. The
direct `wlink` readiness and SDI-output probe remains covered separately by
`ch32v307_composite_runner_spec.spl`.

## Syntax

```simple
val result = run_test_file_jit_ch32v307(
    "test/fixtures/remote_jit/baremetal_lib_workload_main.spl",
    source,
    default_options()
)
```

## Examples

```simple
expect(result.error.contains("not implemented")).to_equal(false)
expect(result.skipped).to_equal(0)
```

## Scenarios

### CH32V307 composite runner path

<details>
<summary>Advanced: does not return the old not-implemented placeholder</summary>

#### does not return the old not-implemented placeholder _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.error.contains("not implemented")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: skips cleanly when wlink or hardware is unavailable</summary>

#### skips cleanly when wlink or hardware is unavailable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if wlink_available() and ch32v307_detected():
    print "[skip] live hardware path available on this host"
    return
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.skipped).to_equal(1)
expect(result.failed).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: uses the real adapter-backed execution path when hardware is available</summary>

#### uses the real adapter-backed execution path when hardware is available _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.skipped).to_equal(0)
expect(result.error.contains("not implemented")).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [[doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)]([doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md))
- **Design:** [[doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)]([doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md))


</details>
