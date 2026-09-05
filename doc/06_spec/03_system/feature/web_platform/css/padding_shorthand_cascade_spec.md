# CSS Padding Shorthand Cascade

> This bounded integer-pixel scenario proves authored source order across the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Padding Shorthand Cascade

This bounded integer-pixel scenario proves authored source order across the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded integer-pixel scenario proves authored source order across the
physical and horizontal-LTR logical padding family, plus invalid-shorthand
rejection, through canonical Web semantics, layout, Draw IR, and Engine2D.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS padding cascade

#### should resolve physical and logical padding in authored order

- should resolve physical and logical padding in authored order
   - Artifact capture: after_step
- Resolve authored padding order in canonical Web semantic style
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: result.hit_index.nodes[shorthand_index].tag equals `div`
   - Expected: result.hit_index.nodes[mixed_index].tag equals `div`
   - Expected: result.hit_index.nodes[invalid_index].tag equals `div`
- Carry the source-order winners into exact layout geometry
   - Artifact capture: after_step
- Retain the winners in canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: result.composition.batches[0].source.source_kind equals `html_ast`
- Render the distinct cascade outcomes through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: _padding_color_count(rendered.pixels, 0xFF2563EBu32) equals `288`
   - Expected: _padding_color_count(rendered.pixels, 0xFFDC2626u32) equals `180`
   - Expected: _padding_color_count(rendered.pixels, 0xFF16A34Au32) equals `528`


<details>
<summary>Executable SSpec</summary>

Runnable source: 86 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-003/004/021
# @req REQ-SSPEC-SYSTEM
step("should resolve physical and logical padding in authored order")
step("Resolve authored padding order in canonical Web semantic style")
val result = simple_web_layout_render_html_draw_ir_result(
    PADDING_CASCADE_HTML, 64, 56
)
val shorthand_index = _padding_node_index(result, "later-shorthand")
val mixed_index = _padding_node_index(result, "mixed")
val invalid_index = _padding_node_index(result, "invalid")
expect(result.hit_index.nodes[shorthand_index].tag).to_equal("div")
expect(result.hit_index.nodes[mixed_index].tag).to_equal("div")
expect(result.hit_index.nodes[invalid_index].tag).to_equal("div")
val shorthand_style = result.hit_index.styles[shorthand_index]
val mixed_style = result.hit_index.styles[mixed_index]
val invalid_style = result.hit_index.styles[invalid_index]
expect([
    shorthand_style.pad_t, shorthand_style.pad_r,
    shorthand_style.pad_b, shorthand_style.pad_l
]).to_equal([4, 5, 4, 5])
expect([
    mixed_style.pad_t, mixed_style.pad_r,
    mixed_style.pad_b, mixed_style.pad_l
]).to_equal([1, 2, 3, 5])
expect([
    invalid_style.pad_t, invalid_style.pad_r,
    invalid_style.pad_b, invalid_style.pad_l
]).to_equal([6, 7, 8, 9])

step("Carry the source-order winners into exact layout geometry")
val boxes = result.hit_index.boxes
expect([
    boxes.bx[shorthand_index], boxes.by[shorthand_index],
    boxes.bw[shorthand_index], boxes.bh[shorthand_index]
]).to_equal([0, 0, 18, 16])
expect([
    boxes.bx[mixed_index], boxes.by[mixed_index],
    boxes.bw[mixed_index], boxes.bh[mixed_index]
]).to_equal([0, 16, 15, 12])
expect([
    boxes.bx[invalid_index], boxes.by[invalid_index],
    boxes.bw[invalid_index], boxes.bh[invalid_index]
]).to_equal([0, 28, 24, 22])

step("Retain the winners in canonical Draw IR")
val shorthand = _padding_command(result, "later-shorthand")
val mixed = _padding_command(result, "mixed")
val invalid = _padding_command(result, "invalid")
expect(result.composition.batches[0].source.source_kind).to_equal("html_ast")
expect([shorthand.x, shorthand.y, shorthand.width, shorthand.height]).to_equal(
    [0, 0, 18, 16]
)
expect([mixed.x, mixed.y, mixed.width, mixed.height]).to_equal(
    [0, 16, 15, 12]
)
expect([invalid.x, invalid.y, invalid.width, invalid.height]).to_equal(
    [0, 28, 24, 22]
)
expect([
    _padding_style(shorthand, "padding-top"),
    _padding_style(shorthand, "padding-right"),
    _padding_style(shorthand, "padding-bottom"),
    _padding_style(shorthand, "padding-left")
]).to_equal(["4", "5", "4", "5"])
expect([
    _padding_style(mixed, "padding-top"),
    _padding_style(mixed, "padding-right"),
    _padding_style(mixed, "padding-bottom"),
    _padding_style(mixed, "padding-left")
]).to_equal(["1", "2", "3", "5"])
expect([
    _padding_style(invalid, "padding-top"),
    _padding_style(invalid, "padding-right"),
    _padding_style(invalid, "padding-bottom"),
    _padding_style(invalid, "padding-left")
]).to_equal(["6", "7", "8", "9"])

step("Render the distinct cascade outcomes through Engine2D")
val raster = Engine2dCompositorBackend.create_named(64, 56, "software")
val rendered = raster.render_draw_ir_composition(result.composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_padding_color_count(rendered.pixels, 0xFF2563EBu32)).to_equal(288)
expect(_padding_color_count(rendered.pixels, 0xFFDC2626u32)).to_equal(180)
expect(_padding_color_count(rendered.pixels, 0xFF16A34Au32)).to_equal(528)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b90c82497d730a33e61510b30c532f5e44a62f80ddcdc17b3864bdc0ccc96046`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b90c82497d730a33e61510b30c532f5e44a62f80ddcdc17b3864bdc0ccc96046`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b90c82497d730a33e61510b30c532f5e44a62f80ddcdc17b3864bdc0ccc96046`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve physical and logical padding in authored order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve physical and logical padding in authored order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
