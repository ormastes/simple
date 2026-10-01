# draw_ir_text_memory_perf_spec

> Semantic Draw IR multilingual text construction/composition smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# draw_ir_text_memory_perf_spec

Semantic Draw IR multilingual text construction/composition smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Semantic Draw IR multilingual text construction/composition smoke.

## Scenarios

### semantic Draw IR text memory performance
_Measures semantic payload construction without claiming renderer work._

#### constructs multilingual shaped commands and composition plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "Aé한😀"
val payload = draw_ir_glyph_run_payload(
    [65u32, 233u32, 54620u32, 128512u32],
    [0, 8, 16, 24], [0, 0, 0, 0], [0, 1, 3, 6], true)
val embedding = draw_ir_embedding_config(
    "surface", "panel", 0, 0, 1024, 768, 1, 1000, true)
var samples: [i64] = []
var checksum: i64 = 0
var sample: i64 = 0
while sample < 7:
    val started = time_now_unix_micros()
    var commands: [DrawIrCommand] = []
    var i: i64 = 0
    while i < 256:
        commands.push(draw_ir_text_shaped_font(
            "label-{i}", (i % 32) as i32, (i / 32) as i32,
            value, 0xffffffffu32, "Noto Sans", "font-id",
            [8, 8, 8, 8], 32, 16, 14, payload))
        i = i + 1
    val batch = draw_ir_batch(
        "text-batch", DRAW_IR_BACKEND_GPU, embedding, commands)
    val composition = draw_ir_composition(
        "scene", "revision", DRAW_IR_BACKEND_GPU, [batch])
    val plan = simple_2d_draw_ir_adv_composition_plan(composition, false)
    checksum = checksum + plan.command_count + commands[255].glyph_run.glyph_ids.len()
    samples.push(time_now_unix_micros() - started)
    sample = sample + 1
val latency = draw_ir_perf_percentiles(samples)
val hwm = draw_ir_perf_hwm_kib()
expect(latency[1]).to_be_less_than(5000001)
expect(hwm).to_be_greater_than(0)
expect(checksum).to_equal(1820)
print "text_perf operation=draw_ir_text_semantic_build samples=7" +
    " commands_per_sample=256 glyphs_per_command=4 source_bytes={value.len()}" +
    " p50_us={latency[0]} p95_us={latency[1]} process_hwm_kib={hwm}" +
    " allocation_count=unavailable allocated_bytes=unavailable" +
    " retained_bytes=unavailable atlas_bytes=0 device_memory_bytes=0" +
    " draw_calls=0 checksum={checksum}"
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

- Canonical SPipe generation for source `3ca4169579bbb82ac78e799b95f7407bd4dca62c8fd9bf58a7eec80d01afd7c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ca4169579bbb82ac78e799b95f7407bd4dca62c8fd9bf58a7eec80d01afd7c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ca4169579bbb82ac78e799b95f7407bd4dca62c8fd9bf58a7eec80d01afd7c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/draw_ir_text_memory_perf_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=90 oracle=90
  traceability=80 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/draw_ir_text_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/draw_ir_text_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/draw_ir_text_memory_perf_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'constructs multilingual shaped commands and composition plans' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
