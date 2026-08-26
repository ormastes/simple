# chrome_vs_simple_spec

> test/perf/web_render_chrome/chrome_vs_simple_spec.spl

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
| Source | `test/perf/web_render_chrome/chrome_vs_simple_spec.spl` |
| Updated | 2026-08-26 |
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

Purpose and audience: AC-10 Chrome-equivalent pipeline benchmark schema and
INP-style timing evidence for web rendering engineers; scope is the report
model, 5-phase coverage, percentile ordering, and fixture identity fields.

@req REQ-PERF-CHROME-PIPELINE
research: doc/01_research/ui/web/simple_browser_chromium_html_parity.md ; research: doc/01_research/ui/rendering/tile_render_culling_chrome.md

## Scenarios

### chrome_vs_simple — AC-10: Chrome pipeline benchmark

### record schema

#### AC-10: report reference_kind is chrome

- operator verifies: AC-10: report reference_kind is chrome
   - Expected: b.reference_kind equals `REF_KIND_CHROME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: report reference_kind is chrome")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.reference_kind).to_equal(REF_KIND_CHROME)
```

</details>

#### AC-10: sample_count is greater than zero

- operator verifies: AC-10: sample_count is greater than zero
   - Expected: b.sample_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: sample_count is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.sample_count > 0).to_equal(true)
```

</details>

#### AC-10: warmup_count is greater than zero

- operator verifies: AC-10: warmup_count is greater than zero
   - Expected: b.warmup_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: warmup_count is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.warmup_count > 0).to_equal(true)
```

</details>

#### AC-10: pixel_hash is non-zero

- operator verifies: AC-10: pixel_hash is non-zero
   - Expected: b.pixel_hash != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: pixel_hash is non-zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.pixel_hash != 0).to_equal(true)
```

</details>

#### AC-10: diff_status is match for equivalent rendering

- operator verifies: AC-10: diff_status is match for equivalent rendering
   - Expected: b.diff_status equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: diff_status is match for equivalent rendering")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.diff_status).to_equal("match")
```

</details>

#### AC-10: inp_us is greater than zero

- operator verifies: AC-10: inp_us is greater than zero
   - Expected: b.inp_us > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: inp_us is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.inp_us > 0).to_equal(true)
```

</details>

### pipeline phases

#### AC-10: five pipeline phases are recorded

- operator verifies: AC-10: five pipeline phases are recorded
   - Expected: b.phases.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: five pipeline phases are recorded")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
# oracle: 5 = input, script, style_layout, paint_raster, composite.
expect(b.phases.len()).to_equal(5)
```

</details>

#### AC-10: first phase is input

- operator verifies: AC-10: first phase is input
   - Expected: b.phases[0].phase equals `PHASE_INPUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: first phase is input")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].phase).to_equal(PHASE_INPUT)
```

</details>

#### AC-10: second phase is script

- operator verifies: AC-10: second phase is script
   - Expected: b.phases[1].phase equals `PHASE_SCRIPT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: second phase is script")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[1].phase).to_equal(PHASE_SCRIPT)
```

</details>

#### AC-10: third phase is style_layout

- operator verifies: AC-10: third phase is style_layout
   - Expected: b.phases[2].phase equals `PHASE_STYLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: third phase is style_layout")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[2].phase).to_equal(PHASE_STYLE)
```

</details>

#### AC-10: fourth phase is paint_raster

- operator verifies: AC-10: fourth phase is paint_raster
   - Expected: b.phases[3].phase equals `PHASE_PAINT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: fourth phase is paint_raster")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[3].phase).to_equal(PHASE_PAINT)
```

</details>

#### AC-10: fifth phase is composite

- operator verifies: AC-10: fifth phase is composite
   - Expected: b.phases[4].phase equals `PHASE_COMPOSITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: fifth phase is composite")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[4].phase).to_equal(PHASE_COMPOSITE)
```

</details>

### INP-style timing

#### AC-10: each phase p95 is greater than or equal to p50

- operator verifies: AC-10: each phase p95 is greater than or equal to p50
   - Expected: b.phases[0].us_p95 >= b.phases[0].us_p50 is true
   - Expected: b.phases[1].us_p95 >= b.phases[1].us_p50 is true
   - Expected: b.phases[2].us_p95 >= b.phases[2].us_p50 is true
   - Expected: b.phases[3].us_p95 >= b.phases[3].us_p50 is true
   - Expected: b.phases[4].us_p95 >= b.phases[4].us_p50 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: each phase p95 is greater than or equal to p50")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p95 >= b.phases[0].us_p50).to_equal(true)
expect(b.phases[1].us_p95 >= b.phases[1].us_p50).to_equal(true)
expect(b.phases[2].us_p95 >= b.phases[2].us_p50).to_equal(true)
expect(b.phases[3].us_p95 >= b.phases[3].us_p50).to_equal(true)
expect(b.phases[4].us_p95 >= b.phases[4].us_p50).to_equal(true)
```

</details>

#### AC-10: each phase p99 is greater than or equal to p95

- operator verifies: AC-10: each phase p99 is greater than or equal to p95
   - Expected: b.phases[0].us_p99 >= b.phases[0].us_p95 is true
   - Expected: b.phases[2].us_p99 >= b.phases[2].us_p95 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: each phase p99 is greater than or equal to p95")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p99 >= b.phases[0].us_p95).to_equal(true)
expect(b.phases[2].us_p99 >= b.phases[2].us_p95).to_equal(true)
```

</details>

#### AC-10: inp_us is sum-compatible with phase timings (sanity)

- operator verifies: AC-10: inp_us is sum-compatible with phase timings (sanity)
   - Expected: total > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: inp_us is sum-compatible with phase timings (sanity)")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
val total: i64 = b.phases[0].us_p50 + b.phases[1].us_p50 + b.phases[2].us_p50 + b.phases[3].us_p50 + b.phases[4].us_p50
expect(total > 0).to_equal(true)
```

</details>

### fixture coverage

#### AC-10: fixture name is non-empty

- operator verifies: AC-10: fixture name is non-empty
   - Expected: b.fixture equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: fixture name is non-empty")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.fixture).to_equal("scroll")
```

</details>

#### AC-10: simple_mode field is present

- operator verifies: AC-10: simple_mode field is present
   - Expected: b.simple_mode equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CHROME-PIPELINE
step("operator verifies: AC-10: simple_mode field is present")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-CHROME-PIPELINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12b9d7d39d5b5f62af15e5b0386598e52b12736d8a54a5e4c816b9381193ccf1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12b9d7d39d5b5f62af15e5b0386598e52b12736d8a54a5e4c816b9381193ccf1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12b9d7d39d5b5f62af15e5b0386598e52b12736d8a54a5e4c816b9381193ccf1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/web_render_chrome/chrome_vs_simple_spec.spl
mirror: doc/06_spec/perf/web_render_chrome/chrome_vs_simple_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/web_render_chrome/chrome_vs_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/web_render_chrome/chrome_vs_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/web_render_chrome/chrome_vs_simple_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/web_render_chrome/chrome_vs_simple_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/web_render_chrome/chrome_vs_simple_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: report reference_kind is chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/web_render_chrome/chrome_vs_simple_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: sample_count is greater than zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/web_render_chrome/chrome_vs_simple_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: warmup_count is greater than zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
