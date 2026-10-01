# Widget Draw Ir Glyph Run Specification

> Tests covering widget Draw-IR text runs carry glyphs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Draw Ir Glyph Run Specification

## Scenarios

### widget Draw-IR text runs carry glyphs

#### emits a glyph run for every plain-Latin text command (v2)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a glyph run for every plain-Latin text command (v2)
   - Expected: total > 0 is true
   - Expected: with_glyphs equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits a glyph run for every plain-Latin text command (v2)")
val (total, with_glyphs) = _text_command_stats(_showcase_v2())
# Anti-vacuity: the tree must actually contain text, otherwise
# "all text commands have glyphs" is trivially true of an empty set.
expect(total > 0).to_equal(true)
expect(with_glyphs).to_equal(total)
```

</details>

#### carries those glyphs through to the v3 text-run table

- carries those glyphs through to the v3 text-run table
   - Expected: runs > 0 is true
   - Expected: runs_with_glyphs equals `runs`
   - Expected: total_glyphs > 0 is true
   - Expected: scene.text_runs.glyph_ids.len().to_i64() equals `total_glyphs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries those glyphs through to the v3 text-run table")
val scene = draw_ir_v2_to_v3(_showcase_v2())
var runs: i64 = 0
var runs_with_glyphs: i64 = 0
var total_glyphs: i64 = 0
var i: i64 = 0
while i < scene.commands.len().to_i64():
    val cmd = scene.commands[i]
    if cmd.kind == DRAW_IR_V3_KIND_TEXT:
        runs = runs + 1
        val run = draw_ir_v3_text_run_at(scene.text_runs, cmd.text_run_id)
        if run.present and run.glyph_count > 0u32:
            runs_with_glyphs = runs_with_glyphs + 1
            total_glyphs = total_glyphs + run.glyph_count.to_i64()
    i = i + 1
expect(runs > 0).to_equal(true)
expect(runs_with_glyphs).to_equal(runs)
expect(total_glyphs > 0).to_equal(true)
# The shared glyph table must be populated, not merely counted.
expect(scene.text_runs.glyph_ids.len().to_i64()).to_equal(total_glyphs)
```

</details>

#### rasterizes a glyph-bearing run to real pixels

- rasterizes a glyph-bearing run to real pixels
   - Expected: _lit_pixels(raster_scene_argb(_one_command_scene(cmd), 64, 32)) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rasterizes a glyph-bearing run to real pixels")
val run = draw_ir_glyph_run_payload(
    [0u32, 1u32, 2u32], [2, 8, 14], [12, 12, 12], [0i64, 1i64, 2i64], true)
val cmd = draw_ir_text_shaped_font(
    "t", 2, 5, "ABC", 0xFFFFFFFFu32, "sans", "id", [6, 6, 6], 18, 12, 12, run)
expect(_lit_pixels(raster_scene_argb(_one_command_scene(cmd), 64, 32)) > 0).to_equal(true)
```

</details>

#### rasterizes a zero-glyph run to a BLANK surface (the defect's signature)

- rasterizes a zero-glyph run to a BLANK surface (the defect's signature)
   - Expected: _lit_pixels(raster_scene_argb(_one_command_scene(cmd), 64, 32)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rasterizes a zero-glyph run to a BLANK surface (the defect's signature)")
# This is why a missing glyph run is fatal rather than degraded: the v3
# text run has no string to fall back on, so the consumer draws nothing.
val cmd = draw_ir_text("t", 2, 5, "ABC", 0xFFFFFFFFu32)
expect(_lit_pixels(raster_scene_argb(_one_command_scene(cmd), 64, 32))).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering widget Draw-IR text runs carry glyphs.
- widget Draw-IR text runs carry glyphs

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

- Canonical SPipe generation for source `d3694f6c6cf669f1dc76c9f0eebd101e8bf5c054d8270d9c992fb7ec601a6b2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3694f6c6cf669f1dc76c9f0eebd101e8bf5c054d8270d9c992fb7ec601a6b2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3694f6c6cf669f1dc76c9f0eebd101e8bf5c054d8270d9c992fb7ec601a6b2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a glyph run for every plain-Latin text command (v2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries those glyphs through to the v3 text-run table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rasterizes a glyph-bearing run to real pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
