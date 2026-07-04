# report_spec

> test/perf/graphics_2d/report_spec.spl

<!-- sdn-diagram:id=report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

report_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# report_spec

test/perf/graphics_2d/report_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | NFR-GRAPHICS-2B, NFR-GRAPHICS-BENCH-REPORT |
| Category | Performance \| Graphics \| Benchmark |
| Status | Active |
| Source | `test/05_perf/graphics_2d/report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/report_spec.spl

Structural validation of the C vs Simple 2D CPU scalar benchmark harness.
Runs on a tiny (8x8) push-based framebuffer — interpreter-safe.

Hard assertions:
  - BenchReport has all required NFR-2B fields
  - frame_count > 0, pixel_hash != 0
  - pixel hash is deterministic (same result on two runs)
  - different scenes produce different hashes
  - NFR_RATIO_THRESHOLD = 1250 (1.25x)
  - canonical scene list has exactly 3 entries

Soft (recorded, not failing):
  - simple_vs_c_ratio <= 1250 — checked at integration time with C output

Integration workflow:
  1. cd test/perf/graphics_2d/c_reference && make && ./bench_2d > /tmp/c_out.txt
  2. SIMPLE_ENGINE2D_RUNNER_MODE=full bin/simple test/perf/graphics_2d/simple_runner.spl > /tmp/s_out.txt
  4. Compare pixel_hash per scene (hard gate: must match)
  5. Compute ratio = simple_p50_ns / c_p50_ns * 1000 (NFR-2B: <= 1250)

## Scenarios

### Graphics 2D CPU benchmark — NFR-GRAPHICS-2B harness

#### scene coverage

#### fill_1080p result has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(0, "fill_1080p")
expect(r.scene_name).to_equal("fill_1080p")
expect(r.frame_count > 0).to_equal(true)
expect(r.pixel_hash != 0).to_equal(true)
expect(r.backend).to_equal("simple_cpu_scalar")
```

</details>

#### blit_tiles result has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(1, "blit_tiles")
expect(r.scene_name).to_equal("blit_tiles")
expect(r.frame_count > 0).to_equal(true)
expect(r.pixel_hash != 0).to_equal(true)
```

</details>

#### clipped_scroll result has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(2, "clipped_scroll")
expect(r.scene_name).to_equal("clipped_scroll")
expect(r.frame_count > 0).to_equal(true)
expect(r.pixel_hash != 0).to_equal(true)
```

</details>

#### report field completeness

#### fill_1080p report fields are all present and self-consistent

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(0, "fill_1080p")
expect(r.pixels_per_sec >= 0).to_equal(true)
expect(r.draws_per_sec >= 0).to_equal(true)
expect(r.p95_ms >= r.p50_ms).to_equal(true)
emit_report(r)
```

</details>

#### blit_tiles report fields are self-consistent

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(1, "blit_tiles")
expect(r.pixels_per_sec >= 0).to_equal(true)
expect(r.p95_ms >= r.p50_ms).to_equal(true)
emit_report(r)
```

</details>

#### clipped_scroll report fields are self-consistent

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(2, "clipped_scroll")
expect(r.pixels_per_sec >= 0).to_equal(true)
expect(r.p95_ms >= r.p50_ms).to_equal(true)
emit_report(r)
```

</details>

#### pixel hash determinism

#### fill_1080p hash is stable across two runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1: BenchReport = tiny_bench(0, "fill_1080p")
val r2: BenchReport = tiny_bench(0, "fill_1080p")
expect(r1.pixel_hash).to_equal(r2.pixel_hash)
```

</details>

#### blit_tiles hash is stable across two runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1: BenchReport = tiny_bench(1, "blit_tiles")
val r2: BenchReport = tiny_bench(1, "blit_tiles")
expect(r1.pixel_hash).to_equal(r2.pixel_hash)
```

</details>

#### clipped_scroll hash is stable across two runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1: BenchReport = tiny_bench(2, "clipped_scroll")
val r2: BenchReport = tiny_bench(2, "clipped_scroll")
expect(r1.pixel_hash).to_equal(r2.pixel_hash)
```

</details>

#### different scenes produce different pixel hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r0: BenchReport = tiny_bench(0, "fill_1080p")
val r1: BenchReport = tiny_bench(1, "blit_tiles")
val r2: BenchReport = tiny_bench(2, "clipped_scroll")
expect(r0.pixel_hash == r1.pixel_hash).to_equal(false)
expect(r0.pixel_hash == r2.pixel_hash).to_equal(false)
```

</details>

#### NFR-2B structure

#### ratio threshold constant is 1250 representing 1.25x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NFR_RATIO_THRESHOLD).to_equal(1250)
```

</details>

#### ratio field initializes to -1 before C numbers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(0, "fill_1080p")
expect(r.simple_vs_c_ratio).to_equal(-1)
```

</details>

#### canonical scene list has exactly 3 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SCENES.len()).to_equal(3)
expect(CANONICAL_SCENES[0]).to_equal("fill_1080p")
expect(CANONICAL_SCENES[1]).to_equal("blit_tiles")
expect(CANONICAL_SCENES[2]).to_equal("clipped_scroll")
```

</details>

#### ratio formula: (simple_p50_ns * 1000) / c_p50_ns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_ns: i64 = 1250
val c_ns: i64 = 1000
val ratio: i64 = (simple_ns * 1000) / c_ns
expect(ratio).to_equal(1250)
expect(ratio <= NFR_RATIO_THRESHOLD).to_equal(true)
```

</details>

#### compute_joined fills ratio from real C p50_ns (fill_1080p)

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(0, "fill_1080p")
# c_p50_ns from actual bench_2d run: 6146240 ns
val joined: BenchReport = compute_joined(r, 6146240)
expect(joined.simple_vs_c_ratio != -1).to_equal(true)
expect(joined.simple_vs_c_ratio > 0).to_equal(true)
emit_report(joined)
```

</details>

#### compute_joined fills ratio from real C p50_ns (blit_tiles)

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(1, "blit_tiles")
# c_p50_ns from actual bench_2d run: 7541685 ns
val joined: BenchReport = compute_joined(r, 7541685)
expect(joined.simple_vs_c_ratio != -1).to_equal(true)
expect(joined.simple_vs_c_ratio > 0).to_equal(true)
emit_report(joined)
```

</details>

#### compute_joined fills ratio from real C p50_ns (clipped_scroll)

1. emit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(2, "clipped_scroll")
# c_p50_ns from actual bench_2d run: 3194512 ns
val joined: BenchReport = compute_joined(r, 3194512)
expect(joined.simple_vs_c_ratio != -1).to_equal(true)
expect(joined.simple_vs_c_ratio > 0).to_equal(true)
emit_report(joined)
```

</details>

#### p50_ns field is present in BenchReport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: BenchReport = tiny_bench(0, "fill_1080p")
expect(r.p50_ns >= 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
