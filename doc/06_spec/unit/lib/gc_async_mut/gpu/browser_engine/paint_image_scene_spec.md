# Paint Image Scene Specification

> Tests covering Browser Paint Image Scene Bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Image Scene Specification

## Scenarios

### Browser Paint Image Scene Bridge

#### converts image paint commands into scene image commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts image paint commands into scene image commands
   - Expected: scene.commands.len() equals `1`
   - Expected: scene.commands[0].kind equals `image`
   - Expected: scene.commands[0].x equals `4`
   - Expected: scene.commands[0].y equals `6`
   - Expected: scene.commands[0].width equals `20`
   - Expected: scene.commands[0].height equals `10`
   - Expected: scene.commands[0].pixel_width equals `2`
   - Expected: scene.commands[0].pixel_height equals `2`
   - Expected: scene.commands[0].pixels.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts image paint commands into scene image commands")
val pixels = [0xFFFF0000u32, 0xFF00FF00u32, 0xFF0000FFu32, 0xFFFFFFFFu32]
val scene = paint_commands_to_scene([
    PaintCommand.image(4, 6, 20, 10, pixels, 2, 2)
], 64, 64)
expect(scene.commands.len()).to_equal(1)
expect(scene.commands[0].kind).to_equal("image")
expect(scene.commands[0].x).to_equal(4)
expect(scene.commands[0].y).to_equal(6)
expect(scene.commands[0].width).to_equal(20)
expect(scene.commands[0].height).to_equal(10)
expect(scene.commands[0].pixel_width).to_equal(2)
expect(scene.commands[0].pixel_height).to_equal(2)
expect(scene.commands[0].pixels.len()).to_equal(4)
```

</details>

#### skips image paint commands without source pixels

- skips image paint commands without source pixels
   - Expected: scene.commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips image paint commands without source pixels")
val scene = paint_commands_to_scene([
    PaintCommand.image(4, 6, 20, 10, [], 0, 0)
], 64, 64)
expect(scene.commands.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser Paint Image Scene Bridge.
- Browser Paint Image Scene Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58de5f0b46a995cb7787a10aaed2007e23ab0505cb9743f4a3a6f9a6d9f0ef67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58de5f0b46a995cb7787a10aaed2007e23ab0505cb9743f4a3a6f9a6d9f0ef67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58de5f0b46a995cb7787a10aaed2007e23ab0505cb9743f4a3a6f9a6d9f0ef67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts image paint commands into scene image commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips image paint commands without source pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
