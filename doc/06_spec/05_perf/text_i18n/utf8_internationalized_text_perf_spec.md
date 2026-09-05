# UTF-8 and internationalized text portable performance baseline

> This retained portable-host lane gives text and release owners reproducible

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UTF-8 and internationalized text portable performance baseline

This retained portable-host lane gives text and release owners reproducible

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/utf8_internationalized_text_architecture.md |
| Plan | doc/03_plan/perf/utf8_internationalized_text_architecture.md |
| Design | doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md |
| Research | doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md |
| Source | `test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This retained portable-host lane gives text and release owners reproducible
latency and memory smoke evidence for current scalar/auto-dispatch UTF-8 scans
and the current UTF-16 conversion path.

## Overview

Corpora are constructed before timing. Twenty-one warm samples are retained so
the median and nearest-rank p95 are observable. Each timed operation contributes
to a deterministic checksum, preventing dead-code elimination and proving that
the measured work completed. Peak RSS is read from the current process after
the workloads.

## Operator workflow

Run this spec on each supported host/profile and retain the emitted lines with
the source, corpus, configuration, toolchain, machine, and active-backend
identity required by `text-i18n-perf-v1`. This source alone is portable host
evidence. It cannot promote a named SIMD backend or physical rendering device.

## Syntax and examples

```text
bin/simple test test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl --mode=interpreter --no-cache
```

## Compatibility and limitations

The bounds are smoke ceilings, not matched-machine regression budgets. The
typed performance contract separately rejects unmatched baselines and memory
growth. Allocation counts and device memory require instrumented production
runners. UTF-16 conversion currently exposes the intermediate-allocation cost
that the architecture plans to remove; this test preserves an honest baseline.

## Evidence and provenance

Printed rows include corpus bytes, sample count, p50/p95 microseconds, checksum,
and peak RSS. Release evidence must wrap these measurements in a complete typed
receipt. Unavailable architecture/device rows remain blocked.

## Metric definitions

- `p50_us` is the middle value after sorting twenty-one warm samples.
- `p95_us` is nearest-rank sample nineteen of twenty-one using zero-based index
  eighteen.
- `input_units` counts UTF-16 code units rather than Unicode scalars or bytes.
- `ascii_bytes` and `mixed_bytes` are exact input byte counts prepared before
  the timer starts.
- `peak_rss_kib` is Linux `VmHWM` for the complete test process; it is an upper
  bound containing runner, compiler/runtime, corpora, and test allocations.
- `checksum` aggregates result sizes/counts so the measured calls are observable.

## Corpus construction

The ASCII corpus cycles `A` through `Z` to exactly 65,536 bytes. The mixed
corpus repeats ASCII `A`, precomposed `é`, Korean `한`, and monochrome emoji
`U+1F600` to the largest complete ten-byte unit below 65,536 bytes. The UTF-16
corpus repeats those scalar classes using one surrogate pair for the emoji.
No malformed sequence is included in this throughput lane; malformed and chunk
partition behavior belongs to correctness and fuzz suites.

## Reproducibility rules

1. Build corpora outside all timed regions.
2. Use the same source revision, corpus hash, configuration hash, manifest hash,
   profile, toolchain, machine, hardware, and active backend for comparisons.
3. Record all twenty-one samples even when an outlier occurs.
4. Keep timer resolution in microseconds explicit; do not relabel it nanoseconds.
5. Run forced-backend lanes separately and attest the backend actually executed.
6. Do not compare interpreter evidence with native evidence as a regression pair.
7. Preserve stdout and the typed receipt beside the summarized result.

## Pass and fail interpretation

A green smoke ceiling proves only that this host completed the portable workload
within a broad safety bound. It does not prove improvement. A matched receipt
comparison must also pass latency and every memory dimension. A zero baseline
for allocations, uploads, index bytes, or noalloc capacity failures remains an
exact zero invariant. Faster execution cannot compensate for higher retained
memory, linked data, atlas waste, VRAM, or peak RSS beyond its selected budget.

## Findings and remediation

The initial retained run found UTF-16 conversion near one second p95 for 32,765
code units. The current implementation first materializes an integer code-point
array and then produces UTF-8. The open tracking record is
`doc/08_tracking/bug/utf16_to_utf8_intermediate_array_perf_2026-08-26.md`.

The required remedy is direct stateful decoding into `TextSink`, with strict
typed errors, split-chunk parity, bounded output progress, and no scalar-count
intermediate allocation. The old implementation remains a differential oracle
until the replacement achieves full branch coverage and matched before/after
receipts.

## Future matrix

This portable file is the first retained row, not the complete performance
matrix. Follow-on runners must cover scalar, SSE2, AVX2, AVX-512, NEON, RVV,
parser ASCII/multilingual paths, default/multilocale message formatting,
Engine2D CPU/Vulkan/CUDA/Metal, and Engine3D HUD/world CPU/Vulkan. Physical
device rows require queue completion and device-origin readback. Unsupported or
unavailable hosts remain blocked and visible.

## Scenarios

### UTF-8 internationalized text portable performance

#### should keep valid scalar access near the legacy ASCII byte-slice cost

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep valid scalar access near the legacy ASCII byte-slice cost
   - Expected: scalar_checksum equals `legacy_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should keep valid scalar access near the legacy ASCII byte-slice cost")
val value = "abcdefghijklmnopqrstuvwxyz0123456789"
val iterations: i64 = 4096
var legacy_samples: [i64] = []
var scalar_samples: [i64] = []
var legacy_checksum: i64 = 0
var scalar_checksum: i64 = 0
var sample: i64 = 0
while sample < PERF_SAMPLES:
    var i: i64 = 0
    val legacy_started = time_now_unix_micros()
    while i < iterations:
        legacy_checksum = legacy_checksum +
            perf_legacy_ascii_char_at(value, i % value.len()).char_code_at(0)
        i = i + 1
    legacy_samples.push(time_now_unix_micros() - legacy_started)
    i = 0
    val scalar_started = time_now_unix_micros()
    while i < iterations:
        scalar_checksum = scalar_checksum +
            str_char_at(value, i % value.len()).char_code_at(0)
        i = i + 1
    scalar_samples.push(time_now_unix_micros() - scalar_started)
    sample = sample + 1
val legacy_latency = perf_p50_p95(legacy_samples)
val scalar_latency = perf_p50_p95(scalar_samples)
expect(scalar_checksum).to_equal(legacy_checksum)
expect(legacy_latency[1]).to_be_greater_than(0)
expect(scalar_latency[1]).to_be_greater_than(0)
expect(scalar_latency[1] * 100).to_be_less_than(legacy_latency[1] * 201)
print "text_perf operation=ascii_char_at samples={PERF_SAMPLES} iterations={iterations} legacy_p50_us={legacy_latency[0]} legacy_p95_us={legacy_latency[1]} scalar_p50_us={scalar_latency[0]} scalar_p95_us={scalar_latency[1]} checksum={scalar_checksum}"
```

</details>

#### should retain ASCII and multilingual scan latency with exact results

- should retain ASCII and multilingual scan latency with exact results


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should retain ASCII and multilingual scan latency with exact results")
val ascii = perf_ascii_bytes()
val multilingual = perf_multilingual_bytes()
var ascii_samples: [i64] = []
var mixed_samples: [i64] = []
var checksum: i64 = 0
var sample: i64 = 0
while sample < PERF_SAMPLES:
    val ascii_started = time_now_unix_micros()
    val ascii_valid = utf8_is_valid(ascii)
    val ascii_count = utf8_count_codepoints(ascii)
    ascii_samples.push(time_now_unix_micros() - ascii_started)
    val mixed_started = time_now_unix_micros()
    val mixed_valid = utf8_is_valid(multilingual)
    val mixed_count = utf8_count_codepoints(multilingual)
    mixed_samples.push(time_now_unix_micros() - mixed_started)
    expect(ascii_valid).to_be(true)
    expect(mixed_valid).to_be(true)
    checksum = checksum + ascii_count + mixed_count
    sample = sample + 1
val ascii_latency = perf_p50_p95(ascii_samples)
val mixed_latency = perf_p50_p95(mixed_samples)
expect(checksum).to_be_greater_than(0)
expect(ascii_latency[1]).to_be_less_than(500001)
expect(mixed_latency[1]).to_be_less_than(500001)
print "text_perf operation=utf8_scan samples={PERF_SAMPLES} ascii_bytes={ascii.len()} mixed_bytes={multilingual.len()} ascii_p50_us={ascii_latency[0]} ascii_p95_us={ascii_latency[1]} mixed_p50_us={mixed_latency[0]} mixed_p95_us={mixed_latency[1]} checksum={checksum}"
```

</details>

#### should retain UTF-16 to UTF-8 conversion latency and bounded host memory

- should retain UTF-16 to UTF-8 conversion latency and bounded host memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should retain UTF-16 to UTF-8 conversion latency and bounded host memory")
val units = perf_utf16_units()
var samples: [i64] = []
var checksum: i64 = 0
var sample: i64 = 0
while sample < PERF_SAMPLES:
    val started = time_now_unix_micros()
    val encoded = utf16_to_utf8(units)
    samples.push(time_now_unix_micros() - started)
    checksum = checksum + encoded.len()
    sample = sample + 1
val latency = perf_p50_p95(samples)
val rss_kib = perf_peak_rss_kib()
expect(checksum).to_be_greater_than(0)
# Calibrated above the retained 2026-08-26 portable-host baseline of
# 1,007,846 us. Matched-machine regressions use the typed delta gate;
# direct streaming conversion is tracked as a production optimization.
expect(latency[1]).to_be_less_than(1250001)
expect(rss_kib).to_be_greater_than(0)
expect(rss_kib).to_be_less_than(524289)
print "text_perf operation=utf16_to_utf8 samples={PERF_SAMPLES} input_units={units.len()} p50_us={latency[0]} p95_us={latency[1]} peak_rss_kib={rss_kib} checksum={checksum}"
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

- **Requirements:** `doc/02_requirements/feature/utf8_internationalized_text_architecture.md`
- **Plan:** `doc/03_plan/perf/utf8_internationalized_text_architecture.md`
- **Design:** `doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md`
- **Research:** `doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
- `REQ-001`
- `REQ-004`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a1f65a59e8d0e6bcad8652244e43836753059677ebe14d6a289f952cb72f6df9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1f65a59e8d0e6bcad8652244e43836753059677ebe14d6a289f952cb72f6df9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1f65a59e8d0e6bcad8652244e43836753059677ebe14d6a289f952cb72f6df9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/utf8_internationalized_text_perf_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/05_perf/text_i18n/utf8_internationalized_text_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/utf8_internationalized_text_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep valid scalar access near the legacy ASCII byte-slice cost' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep valid scalar access near the legacy ASCII byte-slice cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:224:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain ASCII and multilingual scan latency with exact results' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:224:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain ASCII and multilingual scan latency with exact results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:253:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain UTF-16 to UTF-8 conversion latency and bounded host memory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl:253:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain UTF-16 to UTF-8 conversion latency and bounded host memory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
