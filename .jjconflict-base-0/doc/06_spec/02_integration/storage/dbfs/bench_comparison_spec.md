# bench_comparison_spec

> Bench Comparison Specification

<!-- sdn-diagram:id=bench_comparison_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bench_comparison_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bench_comparison_spec -> std
bench_comparison_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bench_comparison_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bench_comparison_spec

Bench Comparison Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/bench_comparison_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Bench Comparison Specification

Validates that the benchmark harness includes FAT32, RamFS in all
4 workloads and that the POSIX baseline runner produces BenchResult
with p50/p99 metrics for comparison reporting.

## Scenarios

### Bench Harness — FAT32 coverage

#### AC-6: make_fat32_table returns a MountTable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_fat32_table()
val r = mt.stat("/fat32")
val ok = r.is_ok()
expect(ok).to_equal(true)
```

</details>

#### AC-6: FAT32 driver name present in run_all results

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("fat32")
```

</details>

### Bench Harness — RamFS coverage

#### AC-6: make_ramfs_table returns a MountTable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_ramfs_table()
val r = mt.stat("/ramfs")
val ok = r.is_ok()
expect(ok).to_equal(true)
```

</details>

#### AC-6: RamFS driver name present in run_all results

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("ramfs")
```

</details>

### Bench Harness — workload completeness

#### AC-6: run_all includes metadata_storm workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("metadata_storm")
```

</details>

#### AC-6: run_all includes append_heavy_log workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("append_heavy_log")
```

</details>

#### AC-6: run_all includes random_overwrite workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("random_overwrite")
```

</details>

#### AC-6: run_all includes mmap_read_mostly workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("mmap_read_mostly")
```

</details>

### POSIX Baseline — runner produces results

#### AC-6: run_posix_metadata_storm returns BenchResult with p50

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_posix_metadata_storm()
expect(r.p50_us).to_be_greater_than(0)
```

</details>

#### AC-6: run_posix_append_log returns BenchResult with p99

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_posix_append_log()
expect(r.p99_us).to_be_greater_than(0)
```

</details>

#### AC-6: run_posix_random_overwrite returns BenchResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_posix_random_overwrite()
val name = r.driver_name
expect(name).to_equal("posix")
```

</details>

#### AC-6: run_posix_mmap_read returns BenchResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_posix_mmap_read()
val name = r.driver_name
expect(name).to_equal("posix")
```

</details>

### Bench Comparison — report shape

#### AC-6: run_all results contain p50_us and p99_us fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val first = results[0]
val has_p50 = first.p50_us >= 0
val has_p99 = first.p99_us >= 0
expect(has_p50).to_equal(true)
expect(has_p99).to_equal(true)
```

</details>

#### AC-6: POSIX baseline included alongside Simple drivers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("posix")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
