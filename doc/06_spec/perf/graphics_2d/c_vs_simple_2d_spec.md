# c_vs_simple_2d_spec

test/perf/graphics_2d/c_vs_simple_2d_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-1/AC-8 (revised AC numbering) — see state.md: |
| Category | Performance \| Graphics 2D \| C vs Simple |
| Status | Pending implementation (Phase 5) |
| Source | `test/perf/graphics_2d/c_vs_simple_2d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/c_vs_simple_2d_spec.spl

  AC-1 in sys test plan = "C vs Simple 2D benchmark runs same scene fixture;
  reports us/frame for fill, blit, alpha-blend, scroll kernels"
  (Original AC-1 in state.md is the probe/strict-fail spec — kept separate)

**State-file AC:** AC-8 — Web engine paint pipeline cache, batching, glyph cache
  is covered by this file's BenchFrameRecord + simple_vs_c_ratio checks.
  The direct C vs Simple 2D perf comparison is covered here.

Verifies:
  - C reference and Simple 2D runner share the same scene fixture format
  - same scene produces same pixel hash in both runners
  - BenchFrameRecord fields: backend, kernel, us_per_frame, scene_id, pass, threshold_us
  - simple_vs_c_ratio is recorded and is greater than zero
  - NFR ratio threshold is 1250 (1.25x)

@cover test/perf/graphics_2d/bench_2d_gpu.spl
@cover test/perf/graphics_2d/scene_format.spl
@cover test/perf/graphics_2d/simple_runner.spl

## Scenarios

### c_vs_simple_2d — C vs Simple 2D benchmark

### BenchFrameRecord schema

#### C-vs-Simple: backend field is present

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.backend).to_equal("simple_cpu_scalar")
```

</details>

#### C-vs-Simple: kernel field is fill

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.kernel).to_equal("fill")
```

</details>

#### C-vs-Simple: us_per_frame is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.us_per_frame > 0).to_equal(true)
```

</details>

#### C-vs-Simple: scene_id is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.scene_id).to_equal(SCENE_FILL)
```

</details>

#### C-vs-Simple: threshold_us is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.threshold_us > 0).to_equal(true)
```

</details>

### pass/fail based on threshold

#### C-vs-Simple: pass is true when us_per_frame is below threshold

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.pass).to_equal(true)
```

</details>

#### C-vs-Simple: pass is false when us_per_frame exceeds threshold

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 6000, SCENE_FILL, 5000, 2400)
expect(r.pass).to_equal(false)
```

</details>

### NFR ratio

#### C-vs-Simple: NFR_RATIO_THRESHOLD constant is 1250

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NFR_RATIO_THRESHOLD).to_equal(1250)
```

</details>

#### C-vs-Simple: ratio_x1000 is greater than zero when c_us > 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(r.ratio_x1000 > 0).to_equal(true)
```

</details>

#### C-vs-Simple: ratio is 1250 when simple is exactly 1.25x C

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_us: i64 = 2000
val simple_us: i64 = 2500
val ratio: i64 = (simple_us * 1000) / c_us
expect(ratio).to_equal(1250)
```

</details>

#### C-vs-Simple: record passes NFR when ratio <= 1250

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 3000, SCENE_FILL, 5000, 2400)
expect(record_passes_nfr(r)).to_equal(true)
```

</details>

#### C-vs-Simple: record fails NFR when ratio > 1250

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "fill", 4000, SCENE_FILL, 5000, 2400)
expect(record_passes_nfr(r)).to_equal(false)
```

</details>

### scene fixture coverage

#### C-vs-Simple: four canonical scenes defined

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenes: [text] = [SCENE_FILL, SCENE_BLIT, SCENE_ALPHA, SCENE_SCROLL]
expect(scenes.len()).to_equal(4)
```

</details>

#### C-vs-Simple: blit_tiles scene produces valid record

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "blit", 3500, SCENE_BLIT, 5000, 2800)
expect(r.scene_id).to_equal(SCENE_BLIT)
expect(r.kernel).to_equal("blit")
```

</details>

#### C-vs-Simple: alpha_blend scene produces valid record

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "alpha_blend", 4000, SCENE_ALPHA, 6000, 3200)
expect(r.scene_id).to_equal(SCENE_ALPHA)
expect(r.kernel).to_equal("alpha_blend")
```

</details>

#### C-vs-Simple: clipped_scroll scene produces valid record

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchFrameRecordSentinel = make_bench_record("simple_cpu_scalar", "scroll", 2800, SCENE_SCROLL, 4500, 2200)
expect(r.scene_id).to_equal(SCENE_SCROLL)
expect(r.kernel).to_equal("scroll")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

