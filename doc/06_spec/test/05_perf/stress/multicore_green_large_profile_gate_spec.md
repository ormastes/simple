# Multicore Green Large Profile Gate

> This spec gates the dated large cross-language profile generated from the canonical profile harness. It focuses on the large fanout behavior that matters for Go-like M:N evidence: Go goroutines should beat one-pthread-per-task C, and Simple `multicore_green_spawn` should use the runtime pool for every logical task while beating the C pthread fanout baseline.

<!-- sdn-diagram:id=multicore_green_large_profile_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_large_profile_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_large_profile_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_large_profile_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Large Profile Gate

This spec gates the dated large cross-language profile generated from the canonical profile harness. It focuses on the large fanout behavior that matters for Go-like M:N evidence: Go goroutines should beat one-pthread-per-task C, and Simple `multicore_green_spawn` should use the runtime pool for every logical task while beating the C pthread fanout baseline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-perf-large-profile-gate |
| Category | Performance / Concurrency |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/01_research/lib/threading/go_vs_simple_threads.md |
| Source | `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec gates the dated large cross-language profile generated from the
canonical profile harness. It focuses on the large fanout behavior that matters
for Go-like M:N evidence: Go goroutines should beat one-pthread-per-task C, and
Simple `multicore_green_spawn` should use the runtime pool for every logical
task while beating the C pthread fanout baseline.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Research

**Research:** doc/01_research/lib/threading/go_vs_simple_threads.md

## Scenarios

### multicore green large cross-language profile gate

#### records the large profile dimensions and runtime-pool evidence

1. Check the profile used large worker counts
2. Check every multicore-green native row reports runtime-pool usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/cross_language_perf_parallel_large_2026-06-07.md") ?? ""
val parallel = section_named(report, "OS Thread Parallel Workers")
val fanout = section_named(report, "Large Fanout Scheduling")
val stress = section_named(report, "Simple vs Go vs C Large Fanout Stress")

step("Check the profile used large worker counts")
expect(report).to_contain("CPU workers:** 100")
expect(report).to_contain("Fanout workers:** 1000")
expect(report).to_contain("Fanout stress workers:** 2000")

step("Check every multicore-green native row reports runtime-pool usage")
expect(model_text(row_for_label(parallel, "Simple multicore green (native)"))).to_contain("pool_used=100/100")
expect(model_text(row_for_label(parallel, "Simple multicore green (native)"))).to_contain("parallelism=64/64")
expect(model_text(row_for_label(fanout, "Simple multicore green (native)"))).to_contain("pool_used=1000/1000")
expect(model_text(row_for_label(stress, "Simple multicore green (native)"))).to_contain("pool_used=2000/2000")
```

</details>

#### proves Go goroutine fanout beats C pthread fanout at large scale

1. Compare Go fanout rows against C pthread rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/cross_language_perf_parallel_large_2026-06-07.md") ?? ""
val fanout = section_named(report, "Large Fanout Scheduling")
val stress = section_named(report, "Simple vs Go vs C Large Fanout Stress")

step("Compare Go fanout rows against C pthread rows")
expect(row_ms_scaled(fanout, "Go")).to_be_less_than(row_ms_scaled(fanout, "C (pthreads)"))
expect(row_ms_scaled(stress, "Go")).to_be_less_than(row_ms_scaled(stress, "C (pthreads)"))
expect(model_text(row_for_label(fanout, "Go"))).to_contain("goroutine per tiny task")
expect(model_text(row_for_label(stress, "Go"))).to_contain("goroutine per stress task")
```

</details>

#### proves Simple multicore-green fanout beats C pthread fanout with pool evidence

1. Compare Simple multicore-green native rows against C pthread rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/cross_language_perf_parallel_large_2026-06-07.md") ?? ""
val fanout = section_named(report, "Large Fanout Scheduling")
val stress = section_named(report, "Simple vs Go vs C Large Fanout Stress")

step("Compare Simple multicore-green native rows against C pthread rows")
expect(row_ms_scaled(fanout, "Simple multicore green (native)")).to_be_less_than(row_ms_scaled(fanout, "C (pthreads)"))
expect(row_ms_scaled(stress, "Simple multicore green (native)")).to_be_less_than(row_ms_scaled(stress, "C (pthreads)"))
expect(model_text(row_for_label(fanout, "Simple multicore green (native)"))).to_contain("parallelism=")
expect(model_text(row_for_label(stress, "Simple multicore green (native)"))).to_contain("parallelism=")
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


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/lib/threading/go_vs_simple_threads.md](doc/01_research/lib/threading/go_vs_simple_threads.md)


</details>
