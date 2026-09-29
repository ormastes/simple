# Simple 2D Vector Font Performance

> Measures 31 paired cold/warm CPU draws of the repository-owned TTF fixture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D Vector Font Performance

Measures 31 paired cold/warm CPU draws of the repository-owned TTF fixture.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Measures 31 paired cold/warm CPU draws of the repository-owned TTF fixture.
Font load, clear, readback, and reporting stay outside timed regions. The
bitmap row requires the pinned host's retained p50 and checksum through
`SIMPLE_2D_BITMAP_BASELINE_NS` and `SIMPLE_2D_BITMAP_BASELINE_CHECKSUM`.

## Scenarios

### Simple 2D vector font performance

#### reuses cached glyphs and improves repeated text rendering

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Paired cold and warm rendering (expected show, folded, detail, or skip)


- reuses cached glyphs and improves repeated text rendering
- Load a vector font fixture
- Render the same text again
- Verify cache and performance evidence
   - Expected: evidence.warm_hits equals `evidence.warm_requests`
   - Expected: evidence.warm_misses equals `0`
   - Expected: evidence.warm_rasterizations equals `0`
   - Expected: evidence.checksum_mismatches equals `0`
   - Expected: evidence.backend equals `cpu`
   - Expected: evidence.bitmap_checksum_mismatches equals `0`
   - Expected: evidence.bitmap_checksum equals `evidence.bitmap_baseline_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("reuses cached glyphs and improves repeated text rendering")
step("Load a vector font fixture")
val evidence = measure_font_performance()

step("Render the same text again")
expect(evidence.cold_p50_ns).to_be_greater_than(0)
expect(evidence.warm_p50_ns).to_be_greater_than(0)
expect(evidence.warm_p50_ns * 100).to_be_less_than(evidence.cold_p50_ns * 75 + 1)

step("Verify cache and performance evidence")
expect(evidence.warm_hits).to_equal(evidence.warm_requests)
expect(evidence.warm_misses).to_equal(0)
expect(evidence.warm_rasterizations).to_equal(0)
expect(evidence.entries).to_be_less_than(513)
expect(evidence.bytes).to_be_less_than(33554433)
expect(evidence.checksum).to_be_greater_than(0)
expect(evidence.checksum_mismatches).to_equal(0)
expect(evidence.backend).to_equal("cpu")
expect(evidence.bitmap_checksum_mismatches).to_equal(0)
expect(evidence.bitmap_baseline_ns).to_be_greater_than(0)
expect(evidence.bitmap_baseline_checksum).to_be_greater_than(0)
expect(evidence.bitmap_checksum).to_equal(evidence.bitmap_baseline_checksum)
expect(evidence.bitmap_p50_ns * 100).to_be_less_than(evidence.bitmap_baseline_ns * 105 + 1)
print "font_perf fixture=ttf-parser-demo license=MIT-OR-Apache-2.0 backend={evidence.backend} viewport=128x72 size=24 samples=31 cold_p50_ns={evidence.cold_p50_ns} cold_p95_ns={evidence.cold_p95_ns} warm_p50_ns={evidence.warm_p50_ns} warm_p95_ns={evidence.warm_p95_ns} bitmap_p50_ns={evidence.bitmap_p50_ns} bitmap_p95_ns={evidence.bitmap_p95_ns} bitmap_checksum={evidence.bitmap_checksum} bitmap_checksum_mismatches={evidence.bitmap_checksum_mismatches} bitmap_baseline_ns={evidence.bitmap_baseline_ns} bitmap_baseline_checksum={evidence.bitmap_baseline_checksum} warm_hits={evidence.warm_hits}/{evidence.warm_requests} warm_misses={evidence.warm_misses} warm_rasterizations={evidence.warm_rasterizations} cache_entries={evidence.entries} cache_bytes={evidence.bytes} checksum={evidence.checksum} checksum_mismatches={evidence.checksum_mismatches} max_rss_kb=outer-harness"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `13b99cf4844319b387a284fc014dd586c8a5edaf95b13f2b096ea7ef180de215`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13b99cf4844319b387a284fc014dd586c8a5edaf95b13f2b096ea7ef180de215`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13b99cf4844319b387a284fc014dd586c8a5edaf95b13f2b096ea7ef180de215`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl
mirror: doc/06_spec/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses cached glyphs and improves repeated text rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
