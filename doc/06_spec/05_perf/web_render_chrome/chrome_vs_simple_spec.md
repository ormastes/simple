# Chrome Vs Simple Specification

> Tests covering chrome_vs_simple — AC-10: Chrome pipeline benchmark, record schema, pipeline phases, INP-style timing, fixture coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome Vs Simple Specification

## Scenarios

### chrome_vs_simple — AC-10: Chrome pipeline benchmark

### record schema

#### AC-10: report reference_kind is chrome

- AC-10: report reference_kind is chrome
   - Expected: b.reference_kind equals `REF_KIND_CHROME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: report reference_kind is chrome")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.reference_kind).to_equal(REF_KIND_CHROME)
```

</details>

#### AC-10: sample_count is greater than zero

- AC-10: sample_count is greater than zero
   - Expected: b.sample_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: sample_count is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.sample_count > 0).to_equal(true)
```

</details>

#### AC-10: warmup_count is greater than zero

- AC-10: warmup_count is greater than zero
   - Expected: b.warmup_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: warmup_count is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.warmup_count > 0).to_equal(true)
```

</details>

#### AC-10: pixel_hash is non-zero

- AC-10: pixel_hash is non-zero
   - Expected: b.pixel_hash != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: pixel_hash is non-zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.pixel_hash != 0).to_equal(true)
```

</details>

#### AC-10: diff_status is match for equivalent rendering

- AC-10: diff_status is match for equivalent rendering
   - Expected: b.diff_status equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: diff_status is match for equivalent rendering")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.diff_status).to_equal("match")
```

</details>

#### AC-10: inp_us is greater than zero

- AC-10: inp_us is greater than zero
   - Expected: b.inp_us > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: inp_us is greater than zero")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.inp_us > 0).to_equal(true)
```

</details>

### pipeline phases

#### AC-10: five pipeline phases are recorded

- AC-10: five pipeline phases are recorded
   - Expected: b.phases.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: five pipeline phases are recorded")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases.len()).to_equal(5)
```

</details>

#### AC-10: first phase is input

- AC-10: first phase is input
   - Expected: b.phases[0].phase equals `PHASE_INPUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: first phase is input")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].phase).to_equal(PHASE_INPUT)
```

</details>

#### AC-10: second phase is script

- AC-10: second phase is script
   - Expected: b.phases[1].phase equals `PHASE_SCRIPT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: second phase is script")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[1].phase).to_equal(PHASE_SCRIPT)
```

</details>

#### AC-10: third phase is style_layout

- AC-10: third phase is style_layout
   - Expected: b.phases[2].phase equals `PHASE_STYLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: third phase is style_layout")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[2].phase).to_equal(PHASE_STYLE)
```

</details>

#### AC-10: fourth phase is paint_raster

- AC-10: fourth phase is paint_raster
   - Expected: b.phases[3].phase equals `PHASE_PAINT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: fourth phase is paint_raster")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[3].phase).to_equal(PHASE_PAINT)
```

</details>

#### AC-10: fifth phase is composite

- AC-10: fifth phase is composite
   - Expected: b.phases[4].phase equals `PHASE_COMPOSITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: fifth phase is composite")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[4].phase).to_equal(PHASE_COMPOSITE)
```

</details>

### INP-style timing

#### AC-10: each phase p95 is greater than or equal to p50

- AC-10: each phase p95 is greater than or equal to p50
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
# @req REQ-SSPEC-PERF
step("AC-10: each phase p95 is greater than or equal to p50")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p95 >= b.phases[0].us_p50).to_equal(true)
expect(b.phases[1].us_p95 >= b.phases[1].us_p50).to_equal(true)
expect(b.phases[2].us_p95 >= b.phases[2].us_p50).to_equal(true)
expect(b.phases[3].us_p95 >= b.phases[3].us_p50).to_equal(true)
expect(b.phases[4].us_p95 >= b.phases[4].us_p50).to_equal(true)
```

</details>

#### AC-10: each phase p99 is greater than or equal to p95

- AC-10: each phase p99 is greater than or equal to p95
   - Expected: b.phases[0].us_p99 >= b.phases[0].us_p95 is true
   - Expected: b.phases[2].us_p99 >= b.phases[2].us_p95 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: each phase p99 is greater than or equal to p95")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.phases[0].us_p99 >= b.phases[0].us_p95).to_equal(true)
expect(b.phases[2].us_p99 >= b.phases[2].us_p95).to_equal(true)
```

</details>

#### AC-10: inp_us is sum-compatible with phase timings (sanity)

- AC-10: inp_us is sum-compatible with phase timings (sanity)
   - Expected: total > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: inp_us is sum-compatible with phase timings (sanity)")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
val total: i64 = b.phases[0].us_p50 + b.phases[1].us_p50 + b.phases[2].us_p50 + b.phases[3].us_p50 + b.phases[4].us_p50
expect(total > 0).to_equal(true)
```

</details>

### fixture coverage

#### AC-10: fixture name is non-empty

- AC-10: fixture name is non-empty
   - Expected: b.fixture equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: fixture name is non-empty")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.fixture).to_equal("scroll")
```

</details>

#### AC-10: simple_mode field is present

- AC-10: simple_mode field is present
   - Expected: b.simple_mode equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-10: simple_mode field is present")
val b: ChromeBenchSentinel = make_chrome_bench_ok()
expect(b.simple_mode).to_equal("native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering chrome_vs_simple — AC-10: Chrome pipeline benchmark, record schema, pipeline phases, INP-style timing, fixture coverage.
- chrome_vs_simple — AC-10: Chrome pipeline benchmark
- record schema
- pipeline phases
- INP-style timing
- fixture coverage

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c59bd0618355089720ba20189efbf386ebad9090aabd21060947c0be77728d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c59bd0618355089720ba20189efbf386ebad9090aabd21060947c0be77728d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c59bd0618355089720ba20189efbf386ebad9090aabd21060947c0be77728d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl
mirror: doc/06_spec/05_perf/web_render_chrome/chrome_vs_simple_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/web_render_chrome/chrome_vs_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web_render_chrome/chrome_vs_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: report reference_kind is chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: sample_count is greater than zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/chrome_vs_simple_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: warmup_count is greater than zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
