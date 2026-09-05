# Draw Ir Target Specification

> Tests covering Draw IR render target seam.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Target Specification

## Scenarios

### Draw IR render target seam

#### keeps Engine2D source-compatible while executing through the target contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps Engine2D source-compatible while executing through the target contract
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[1 * 8 + 2] equals `0xff123456u32`
   - Expected: result.pixels[0] equals `0xff000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Engine2D source-compatible while executing through the target contract")
var engine = Engine2D.create_with_backend(8, 6, "cpu")
engine.clear(0xff000000u32)
val batch = draw_ir_batch(
    "target-seam",
    DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surface", "window", 0, 0, 8, 6, 0, 1000, false),
    [draw_ir_rect("body", 2, 1, 3, 2, 0xff123456u32)]
)
val composition = draw_ir_composition(
    "target-seam", "scene", DRAW_IR_BACKEND_CPU, [batch])

val result = engine2d_draw_ir_adv_composition(
    engine, composition, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[1 * 8 + 2]).to_equal(0xff123456u32)
expect(result.pixels[0]).to_equal(0xff000000u32)
engine.shutdown()
```

</details>

#### composites an offscreen readback through the same target owner

- composites an offscreen readback through the same target owner
   - Expected: reason equals ``
   - Expected: engine.read_pixels()[1 * 6 + 1] equals `0xffff0000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites an offscreen readback through the same target owner")
var engine = Engine2D.create_with_backend(6, 4, "cpu")
engine.clear(0xff000000u32)
val child = engine.draw_ir_create_offscreen(2, 2)

match child:
    Err(reason):
        expect(reason).to_equal("")
    Ok(target):
        target.clear(0xffff0000u32)
        val readback = target.read_pixels_with_source()
        val composited = engine.draw_ir_composite_readback(
            1, 1, 2, 2, readback, 1000)

        expect(composited).to_be(true)
        expect(engine.read_pixels()[1 * 6 + 1]).to_equal(0xffff0000u32)
        target.shutdown()
engine.shutdown()
```

</details>

#### rejects malformed child readback before mutating the destination

- rejects malformed child readback before mutating the destination
   - Expected: engine.read_pixels()[0] equals `0xff010203u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed child readback before mutating the destination")
var engine = Engine2D.create_with_backend(4, 4, "cpu")
engine.clear(0xff010203u32)
val malformed = engine2d_readback(
    [0xffffffffu32], "software")

val composited = engine.draw_ir_composite_readback(
    0, 0, 2, 2, malformed, 1000)

expect(composited).to_be(false)
expect(engine.read_pixels()[0]).to_equal(0xff010203u32)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Draw IR render target seam.
- Draw IR render target seam

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9843831acd3721f98b6fd0f11d48dc1341861bddff9dea866468d957274ec98`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9843831acd3721f98b6fd0f11d48dc1341861bddff9dea866468d957274ec98`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9843831acd3721f98b6fd0f11d48dc1341861bddff9dea866468d957274ec98`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Engine2D source-compatible while executing through the target contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composites an offscreen readback through the same target owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_target_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed child readback before mutating the destination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
