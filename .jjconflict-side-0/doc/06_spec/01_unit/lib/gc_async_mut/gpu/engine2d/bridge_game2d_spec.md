# Bridge Game2d Specification

> Tests covering game2d commands bridged onto the shared Engine2D RenderBackend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bridge Game2d Specification

## Scenarios

### game2d commands bridged onto the shared Engine2D RenderBackend

#### paints clear + filled rect through the cpu_simd (SIMD-CPU) lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- paints clear + filled rect through the cpu_simd (SIMD-CPU) lane
   - Expected: pixels.len() equals `(FB_W * FB_H) as i32`
   - Expected: _at(pixels, 4, 4) equals `red_u32`
   - Expected: _at(pixels, 14, 14) equals `blue_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints clear + filled rect through the cpu_simd (SIMD-CPU) lane")
val pixels = _render(_build_commands(), "cpu_simd")
val red_u32 = _u32_of(EngineColor.red())
val blue_u32 = _u32_of(EngineColor.blue())

# Framebuffer is the full 16x16 surface.
expect(pixels.len()).to_equal((FB_W * FB_H) as i32)
# A pixel INSIDE the rect (4,4) is the rect color.
expect(_at(pixels, 4, 4)).to_equal(red_u32)
# A pixel OUTSIDE the rect (14,14) keeps the clear color.
expect(_at(pixels, 14, 14)).to_equal(blue_u32)
```

</details>

#### paints the same content through the software lane

- paints the same content through the software lane
   - Expected: pixels.len() equals `(FB_W * FB_H) as i32`
   - Expected: _at(pixels, 4, 4) equals `red_u32`
   - Expected: _at(pixels, 14, 14) equals `blue_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints the same content through the software lane")
val pixels = _render(_build_commands(), "software")
val red_u32 = _u32_of(EngineColor.red())
val blue_u32 = _u32_of(EngineColor.blue())

expect(pixels.len()).to_equal((FB_W * FB_H) as i32)
expect(_at(pixels, 4, 4)).to_equal(red_u32)
expect(_at(pixels, 14, 14)).to_equal(blue_u32)
```

</details>

#### maps clear + filled rect without skipping any command

- maps clear + filled rect without skipping any command
   - Expected: bridge_count_unmapped(_build_commands()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps clear + filled rect without skipping any command")
# Clear and DrawRect are both mapped; nothing is dropped.
expect(bridge_count_unmapped(_build_commands())).to_equal(0)
```

</details>

#### maps circle and line primitives, and counts the unmapped DrawTriangles

- maps circle and line primitives, and counts the unmapped DrawTriangles
   - Expected: bridge_count_unmapped(buf) equals `1`
   - Expected: _at(pixels, 8, 8) equals `green_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps circle and line primitives, and counts the unmapped DrawTriangles")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.blue()))
buf.push(RenderCommand.DrawCircle(
    cx: 8.0, cy: 8.0, radius: 4.0,
    color: EngineColor.green(), z_order: ZIndex(value: 0)))
buf.push(RenderCommand.DrawLine(
    x1: 0.0, y1: 0.0, x2: 15.0, y2: 0.0, width: 1.0,
    color: EngineColor.white(), z_order: ZIndex(value: 0)))
buf.push(RenderCommand.DrawTriangles(
    vertices: [], indices: [],
    color: EngineColor.red(), z_order: ZIndex(value: 0)))

# Clear/DrawCircle/DrawLine map; only DrawTriangles is unmapped.
expect(bridge_count_unmapped(buf)).to_equal(1)

# And the mapped circle genuinely paints: center pixel is the circle color.
val pixels = _render(buf, "cpu_simd")
val green_u32 = _u32_of(EngineColor.green())
expect(_at(pixels, 8, 8)).to_equal(green_u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering game2d commands bridged onto the shared Engine2D RenderBackend.
- game2d commands bridged onto the shared Engine2D RenderBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `2431226ac26a571de71c4dd1cd4803ad2355305b2a796ad7bcd02b36fbe1f342`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2431226ac26a571de71c4dd1cd4803ad2355305b2a796ad7bcd02b36fbe1f342`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2431226ac26a571de71c4dd1cd4803ad2355305b2a796ad7bcd02b36fbe1f342`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints clear + filled rect through the cpu_simd (SIMD-CPU) lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints the same content through the software lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps clear + filled rect without skipping any command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
