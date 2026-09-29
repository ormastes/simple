# font_hud_material_memory_perf_spec

> Measures backend-neutral vertex preparation from one immutable shared font

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_hud_material_memory_perf_spec

Measures backend-neutral vertex preparation from one immutable shared font

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Engine3D HUD/world text-material memory performance

Measures backend-neutral vertex preparation from one immutable shared font
batch. This is CPU transient-memory evidence; it does not qualify GPU upload,
queue completion, VRAM, or device readback.

## Scenarios

### Engine3D text-material memory performance
_Proves deterministic transient size and emits bounded host timing evidence._

#### reports exact transient bytes and bounded HUD/world preparation

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val batch = material_perf_batch()
var hud_samples: [i64] = []
var world_samples: [i64] = []
var output_bytes: i64 = 0
var checksum: i64 = 0
var sample: i64 = 0
while sample < 7:
    val hud_started = time_now_unix_micros()
    val hud = font_hud_vertices(batch, 8, 8, 1024, 768)
    hud_samples.push(time_now_unix_micros() - hud_started)
    val world_started = time_now_unix_micros()
    val world = font_world_vertices(batch, 8, 8, 1024, 768, 0.25f32)
    world_samples.push(time_now_unix_micros() - world_started)
    expect(hud.len()).to_equal(64 * 6 * 20)
    expect(world.len()).to_equal(64 * 6 * 24)
    output_bytes = output_bytes + hud.len() + world.len()
    checksum = checksum + hud[0].to_i64() + world[world.len() - 1].to_i64()
    sample = sample + 1
val hud_latency = material_perf_percentiles(hud_samples)
val world_latency = material_perf_percentiles(world_samples)
val hwm = material_perf_hwm_kib()
expect(hud_latency[1]).to_be_less_than(1000001)
expect(world_latency[1]).to_be_less_than(1000001)
expect(hwm).to_be_greater_than(0)
print "text_perf operation=engine3d_font_material samples=7 quads=64 atlas_cpu_bytes=16384 hud_bytes_per_quad=120 world_bytes_per_quad=144 total_output_bytes={output_bytes} hud_p50_us={hud_latency[0]} hud_p95_us={hud_latency[1]} world_p50_us={world_latency[0]} world_p95_us={world_latency[1]} process_hwm_kib={hwm} allocation_count=unavailable device_memory_bytes=unavailable upload_bytes=unavailable queue_completion=unavailable readback=unavailable checksum={checksum}"
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

- Canonical SPipe generation for source `385873998d783e7bcb5825ae1fc09dbb5c4e96049b3c0a0affe0255b16621f69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `385873998d783e7bcb5825ae1fc09dbb5c4e96049b3c0a0affe0255b16621f69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `385873998d783e7bcb5825ae1fc09dbb5c4e96049b3c0a0affe0255b16621f69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/font_hud_material_memory_perf_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=90 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/font_hud_material_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/font_hud_material_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/font_hud_material_memory_perf_spec.spl:53:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports exact transient bytes and bounded HUD/world preparation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
