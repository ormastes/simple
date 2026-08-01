# shared_helpers_spec

> test/perf/graphics_2d/shared_helpers_spec.spl

<!-- sdn-diagram:id=shared_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_helpers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shared_helpers_spec

test/perf/graphics_2d/shared_helpers_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-11 — All benchmarks write structured output to |
| Category | Graphics \| Benchmark \| Shared Helpers |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/shared_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/shared_helpers_spec.spl

  test/perf/graphics_2d/ and test/perf/local_gpu_check/;
  report_spec.spl parses and prints pass/fail vs thresholds.
  (Deduplication: shared BenchFrameRecord schema used by all bench drivers)
Verifies:
  - BenchFrameRecord has a canonical schema used across all bench drivers
  - report_spec.spl can parse records from GPU, SIMD, Tauri-equiv, Chrome-equiv
  - Output paths are well-defined for graphics_2d/ and local_gpu_check/
  - FramePacingCounters fields are correctly initialized
  - WM frame pacing event-sleep is measured and idle_cpu_us is reported

@cover test/perf/graphics_2d/report_spec.spl
@cover test/perf/local_gpu_check/gpu_perf_compare.spl
@cover src/lib/gc_async_mut/gpu/engine2d/wm_frame_pacing.spl

## Scenarios

### shared_helpers — AC-11: shared BenchFrameRecord, output paths, frame pacing

### BenchFrameRecord canonical schema

#### AC-11: backend field stores backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.backend).to_equal("cuda")
```

</details>

#### AC-11: kernel field stores kernel name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.kernel).to_equal("fill")
```

</details>

#### AC-11: us_per_frame field stores microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.us_per_frame).to_equal(800)
```

</details>

#### AC-11: scene_id field stores scene name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.scene_id).to_equal("fill_1080p")
```

</details>

#### AC-11: pass field is true when us_per_frame is below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.pass).to_equal(true)
```

</details>

#### AC-11: pass field is false when us_per_frame exceeds threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 3000, "fill_1080p", 2000)
expect(r.pass).to_equal(false)
```

</details>

#### AC-11: threshold_us field stores threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("cuda", "fill", 800, "fill_1080p", 2000)
expect(r.threshold_us).to_equal(2000)
```

</details>

### output directory paths

#### AC-11: graphics_2d output path is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OUTPUT_DIR_GRAPHICS_2D).to_equal("test/perf/graphics_2d/")
```

</details>

#### AC-11: local_gpu_check output path is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OUTPUT_DIR_LOCAL_GPU_CHECK).to_equal("test/perf/local_gpu_check/")
```

</details>

#### AC-11: output paths are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OUTPUT_DIR_GRAPHICS_2D == OUTPUT_DIR_LOCAL_GPU_CHECK).to_equal(false)
```

</details>

### FramePacingCounters fields

#### AC-11: event_sleep_us field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 3, 1, 1200, 60)
expect(c.event_sleep_us).to_equal(500)
```

</details>

#### AC-11: dirty_rect_count field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 3, 1, 1200, 60)
expect(c.dirty_rect_count).to_equal(3)
```

</details>

#### AC-11: present_batch_count field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 3, 1, 1200, 60)
expect(c.present_batch_count).to_equal(1)
```

</details>

#### AC-11: idle_cpu_us field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 3, 1, 1200, 60)
expect(c.idle_cpu_us).to_equal(1200)
```

</details>

#### AC-11: frame_count field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 3, 1, 1200, 60)
expect(c.frame_count).to_equal(60)
```

</details>

### WM frame pacing — idle CPU budget

#### AC-11: event_sleep_us is greater than zero when frame is idle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 0, 0, 1200, 60)
expect(c.event_sleep_us > 0).to_equal(true)
```

</details>

#### AC-11: idle_cpu_us is greater than zero in an idle frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 0, 0, 1200, 60)
expect(c.idle_cpu_us > 0).to_equal(true)
```

</details>

#### AC-11: dirty_rect_count is zero in an idle frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 0, 0, 1200, 60)
expect(c.dirty_rect_count).to_equal(0)
```

</details>

#### AC-11: present_batch_count is zero in an idle frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_frame_pacing_sentinel(500, 0, 0, 1200, 60)
expect(c.present_batch_count).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
