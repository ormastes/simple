# text_ops_memory_perf_spec

> Mode-aware traversal and display-width latency/memory smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_ops_memory_perf_spec

Mode-aware traversal and display-width latency/memory smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/text_ops_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mode-aware traversal and display-width latency/memory smoke.

## Scenarios

### mode-aware text operation memory performance
_Measures mixed traversal while keeping unavailable counters explicit._

#### traverses ASCII and multilingual text with bounded retained state

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ascii = "Simple UTF-8 parser text 0123456789"
val multilingual = "한국어 العربية हिन्दी 日本語 😀 e\u{0301}"
var samples: [i64] = []
var checksum: i64 = 0
var sample: i64 = 0
while sample < 7:
    val started = time_now_unix_micros()
    var i: i64 = 0
    while i < 256:
        set_char_mode(CharMode.Utf8)
        checksum = checksum + text_len_mode(ascii)
        checksum = checksum + text_slice_mode(ascii, 0, 6).len()
        set_char_mode(CharMode.FullUnicode)
        checksum = checksum + text_len_mode(multilingual)
        checksum = checksum + text_char_at_mode(multilingual, 2).len()
        checksum = checksum + text_chars_mode(multilingual).len()
        checksum = checksum + text_display_width(multilingual)
        i = i + 1
    samples.push(time_now_unix_micros() - started)
    sample = sample + 1
set_char_mode(CharMode.Utf8)
val latency = text_ops_percentiles(samples)
val hwm = text_ops_hwm_kib()
expect(latency[1]).to_be_less_than(5000001)
expect(hwm).to_be_greater_than(0)
expect(checksum).to_be_greater_than(0)
print "text_perf operation=text_ops samples=7 iterations=1792" +
    " ascii_input_bytes={ascii.len()} multilingual_input_bytes={multilingual.len()}" +
    " p50_us={latency[0]} p95_us={latency[1]} process_hwm_kib={hwm}" +
    " allocation_count=unavailable allocated_bytes=unavailable" +
    " retained_bytes=unavailable checkpoint_bytes=0 checksum={checksum}"
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1746e9f25e9a936713438e42c31b51736d6d3636504e462538ec22201edd9ef4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1746e9f25e9a936713438e42c31b51736d6d3636504e462538ec22201edd9ef4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1746e9f25e9a936713438e42c31b51736d6d3636504e462538ec22201edd9ef4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/text_i18n/text_ops_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/text_ops_memory_perf_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=90 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/text_ops_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/text_ops_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/text_ops_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/text_ops_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/text_ops_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/text_ops_memory_perf_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'traverses ASCII and multilingual text with bounded retained state' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
