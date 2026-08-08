# bench_harness_smoke_spec

> BenchHarness Smoke Specification

<!-- sdn-diagram:id=bench_harness_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bench_harness_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bench_harness_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bench_harness_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bench_harness_smoke_spec

BenchHarness Smoke Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/bench_harness_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

BenchHarness Smoke Specification

Quick sanity checks for BenchResult and percentile helpers.
Verifies harness infrastructure compiles and basic math is correct.

## Scenarios

### BenchHarness — smoke (metadata storm, 10 files)

#### metadata_storm over DBFS completes for 10 files

1. drv open path
2. drv unlink path
   - Expected: i equals `10`
   - Expected: post_stat.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbFsDriver.new_hosted()
val paths: [text] = [
    "/smoke_0", "/smoke_1", "/smoke_2", "/smoke_3", "/smoke_4",
    "/smoke_5", "/smoke_6", "/smoke_7", "/smoke_8", "/smoke_9"
]
var i: i64 = 0
for path in paths:
    drv.open_path(Path(raw: path), OpenFlags.create_write()).unwrap()
    drv.unlink_path(path).unwrap()
    i = i + 1
expect(i).to_equal(10)
val post_stat = drv.stat("/smoke_5")
expect(post_stat.is_err()).to_equal(true)
```

</details>

#### BenchResult write_amplification returns 0 when logical_bytes=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = BenchResult(
    workload_name: "test", driver_name: "x",
    p50_us: 0, p99_us: 0, bytes_written: 0, logical_bytes: 0,
    recovery_time_us: 0, mount_time_us: 0, rss_kib: 0, cache_hit_ratio: 0,
)
expect(r.write_amplification()).to_equal(0)
```

</details>

#### percentile of sorted list returns correct element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
val p50 = percentile(data, 50)
expect(p50 >= 50 and p50 <= 60).to_equal(true)
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


</details>
