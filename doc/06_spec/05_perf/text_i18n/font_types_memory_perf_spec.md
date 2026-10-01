# font_types_memory_perf_spec

> Shared font configuration planning and identity memory-performance smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_types_memory_perf_spec

Shared font configuration planning and identity memory-performance smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/font_types_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Shared font configuration planning and identity memory-performance smoke.

## Scenarios

### font configuration memory performance

#### reports bounded planning and identity construction with explicit memory availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = perf_config()
val targets = ["cuda", "metal", "vulkan", "cpu"]
var samples: [i64] = []
var checksum: i64 = 0
var sample: i64 = 0
while sample < 7:
    val started = time_now_unix_micros()
    var iteration: i64 = 0
    while iteration < 256:
        var plan: [text] = []
        val count = font_execution_plan_into(config, targets, plan)
        val identity = font_render_config_identity(config)
        checksum = checksum + count + plan.len() + identity.len()
        iteration = iteration + 1
    samples.push(time_now_unix_micros() - started)
    sample = sample + 1
val latency = perf_percentiles(samples)
val hwm = perf_hwm_kib()
expect(latency[1]).to_be_less_than(1000001)
expect(hwm).to_be_greater_than(0)
expect(checksum).to_be_greater_than(0)
print "text_perf operation=font_types_config samples=7 iterations=1792" +
    " targets=4 p50_us={latency[0]} p95_us={latency[1]}" +
    " process_hwm_kib={hwm} allocation_count=unavailable" +
    " allocated_bytes=unavailable retained_bytes=unavailable" +
    " linked_data_bytes=unavailable checksum={checksum}"
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

- Canonical SPipe generation for source `36e08f6fabb6f5e3f3adf6a64770fc27d8699958f5a4fae146fb3c17f0cbdd94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36e08f6fabb6f5e3f3adf6a64770fc27d8699958f5a4fae146fb3c17f0cbdd94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36e08f6fabb6f5e3f3adf6a64770fc27d8699958f5a4fae146fb3c17f0cbdd94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/text_i18n/font_types_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/font_types_memory_perf_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=90 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/font_types_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/font_types_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/font_types_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/font_types_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/font_types_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/font_types_memory_perf_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports bounded planning and identity construction with explicit memory availability' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
