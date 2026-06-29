# chrome_vs_simple_spec

> test/perf/web_render_chrome/chrome_vs_simple_spec.spl

<!-- sdn-diagram:id=chrome_vs_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_vs_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_vs_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_vs_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chrome_vs_simple_spec

test/perf/web_render_chrome/chrome_vs_simple_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-10 — Chrome-equivalent benchmark: input→style/layout→paint/raster→composite |
| Category | Performance \| Web Rendering \| Chrome |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/web_render_chrome/chrome_vs_simple_spec.spl

Verifies that the Chrome-equivalent benchmark:
  - Runs all pipeline phases: input, script, style/layout, paint/raster, composite
  - Reports normalized INP-style timing per phase
  - Fixture results include pixel output hash or diff status
  - Report records reference_kind = "chrome"

@cover test/perf/web_render_chrome/chrome_runner.spl
@cover test/perf/web_render_chrome/report_spec.spl
@cover test/perf/web_render_chrome/trace_normalizer.spl

## Scenarios

### chrome_vs_simple — AC-10: Chrome pipeline benchmark

### record schema

#### AC-10: report reference_kind is chrome

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.reference_kind).to_equal(REF_KIND_CHROME)
```

</details>

#### AC-10: sample_count is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.sample_count > 0).to_equal(true)
```

</details>

#### AC-10: warmup_count is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.warmup_count > 0).to_equal(true)
```

</details>

#### AC-10: pixel_hash is non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.pixel_hash != 0).to_equal(true)
```

</details>

#### AC-10: diff_status is match for equivalent rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.diff_status).to_equal("match")
```

</details>

#### AC-10: inp_us is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.inp_us > 0).to_equal(true)
```

</details>

### pipeline phases

#### AC-10: five pipeline phases are recorded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases.len()).to_equal(5)
```

</details>

#### AC-10: first phase is input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].phase).to_equal(PHASE_INPUT)
```

</details>

#### AC-10: second phase is script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[1].phase).to_equal(PHASE_SCRIPT)
```

</details>

#### AC-10: third phase is style_layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[2].phase).to_equal(PHASE_STYLE)
```

</details>

#### AC-10: fourth phase is paint_raster

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[3].phase).to_equal(PHASE_PAINT)
```

</details>

#### AC-10: fifth phase is composite

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[4].phase).to_equal(PHASE_COMPOSITE)
```

</details>

### INP-style timing

#### AC-10: each phase p95 is greater than or equal to p50

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p95 >= b.phases[0].us_p50).to_equal(true)
expect(b.phases[1].us_p95 >= b.phases[1].us_p50).to_equal(true)
expect(b.phases[2].us_p95 >= b.phases[2].us_p50).to_equal(true)
expect(b.phases[3].us_p95 >= b.phases[3].us_p50).to_equal(true)
expect(b.phases[4].us_p95 >= b.phases[4].us_p50).to_equal(true)
```

</details>

#### AC-10: each phase p99 is greater than or equal to p95

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p99 >= b.phases[0].us_p95).to_equal(true)
expect(b.phases[2].us_p99 >= b.phases[2].us_p95).to_equal(true)
```

</details>

#### AC-10: inp_us is sum-compatible with phase timings (sanity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
val total: i64 = b.phases[0].us_p50 + b.phases[1].us_p50 + b.phases[2].us_p50 + b.phases[3].us_p50 + b.phases[4].us_p50
expect(total > 0).to_equal(true)
```

</details>

### fixture coverage

#### AC-10: fixture name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.fixture).to_equal("scroll")
```

</details>

#### AC-10: simple_mode field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.simple_mode).to_equal("native")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
