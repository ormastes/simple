# simple_web_iframe_draw_ir_embedding_spec

> Canonical iframe `srcdoc` DrawIR embedding.  This exercises the Web semantic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_web_iframe_draw_ir_embedding_spec

Canonical iframe `srcdoc` DrawIR embedding.  This exercises the Web semantic

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Canonical iframe `srcdoc` DrawIR embedding.  This exercises the Web semantic
owner and the existing Engine2D executor; it deliberately does not migrate the
legacy software-pixel iframe callers before parity evidence exists.

## Scenarios

### Simple Web iframe srcdoc through DrawIR

#### keeps iframe embedding canonical and fail closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps iframe embedding canonical and fail closed
- Compose iframe srcdoc through Web semantics and Draw IR
   - Expected: basic_pixels[5 + 5 * 100] equals `0xFFEF4444u32`
   - Expected: basic_pixels[20 + 20 * 100] equals `0xFF22C55Eu32`
   - Expected: basic_pixels[80 + 50 * 100] equals `0xFFFFFFFFu32`
   - Expected: basic_child.embedding.x equals `0`
   - Expected: basic_child.embedding.y equals `10`
   - Expected: basic_child.embedding.layer equals `0`
   - Expected: basic_child.embedding.component_id equals `iframe_4`
   - Expected: command.hit_rect.present is false
- Preserve iframe paint order and ancestor clipping
   - Expected: _iframe_pixels(overlap_result, 80, 50)[20 + 20 * 80] equals `0xFFEF4444u32`
   - Expected: command.clip_rect.present is true
   - Expected: batch.embedding.layer equals `0`
   - Expected: clipped_pixels[10 + 5 * 60] equals `0xFF22C55Eu32`
   - Expected: clipped_pixels[25 + 5 * 60] equals `0xFFFFFFFFu32`
- Bound nested iframe work and fail closed
   - Expected: _iframe_pixels(simple_web_layout_render_html_draw_ir_result(nested_html, 40, 30), 40, 30)[5 + 5 * 40] equals `0xFFF97316u32`
   - Expected: _iframe_pixels(simple_web_layout_render_html_draw_ir_result(capped, 40, 30), 40, 30)[5 + 5 * 40] equals `0xFF888888u32`
   - Expected: _iframe_opacity_batch_count(fractional_result.composition) equals `1`
   - Expected: fractional_pixels[10 + 10 * 40] equals `0xFFC3C3C3u32`
   - Expected: fractional_pixels[35 + 10 * 40] equals `0xFFF7A2A2u32`
- Retire legacy iframe pixel blitting after parity
   - Expected: _iframe_has_image_or_material_or_hit(basic.composition) is false
   - Expected: _iframe_pixels(inert_result, 40, 30)[5 + 5 * 40] equals `0xFF22C55Eu32`
   - Expected: _iframe_has_image_or_material_or_hit(inert_result.composition) is false
   - Expected: child_scroll_pixels[5 + 5 * 40] equals `0xFFEF4444u32`
   - Expected: child_scroll_pixels[5 + 20 * 40] equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps iframe embedding canonical and fail closed")
step("Compose iframe srcdoc through Web semantics and Draw IR")
val html = "<html><body style='margin:0;padding:0;background-color:#ffffff'><div style='width:10px;height:10px;background-color:#ef4444'></div><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\"></iframe></body></html>"
val basic = simple_web_layout_render_html_draw_ir_result(html, 100, 60)
val basic_pixels = _iframe_pixels(basic, 100, 60)
expect(basic_pixels[5 + 5 * 100]).to_equal(0xFFEF4444u32)
expect(basic_pixels[20 + 20 * 100]).to_equal(0xFF22C55Eu32)
expect(basic_pixels[80 + 50 * 100]).to_equal(0xFFFFFFFFu32)
val basic_child_index = _iframe_child_batch_index(basic.composition)
expect(basic_child_index).to_be_greater_than(0)
val basic_child = basic.composition.batches[basic_child_index]
expect(basic_child.embedding.x).to_equal(0)
expect(basic_child.embedding.y).to_equal(10)
expect(basic_child.embedding.layer).to_equal(0)
expect(basic_child.batch_id).to_start_with("iframe_4:iframe:1:")
expect(basic_child.embedding.surface_id).to_start_with("iframe_4:iframe:1:")
expect(basic_child.embedding.component_id).to_equal("iframe_4")
for command in basic_child.commands:
    expect(command.component_id).to_start_with("iframe_4:iframe:1:")
    expect(command.hit_rect.present).to_equal(false)
    if command.parent_id != "":
        expect(command.parent_id).to_start_with("iframe_4:iframe:1:")

step("Preserve iframe paint order and ancestor clipping")
val overlap = "<html><body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\"></iframe><div style='position:absolute;left:0;top:0;width:40px;height:30px;background-color:#ef4444'></div></body></html>"
val overlap_result = simple_web_layout_render_html_draw_ir_result(overlap, 80, 50)
val child_index = _iframe_child_batch_index(overlap_result.composition)
expect(child_index).to_be_greater_than(0)
expect(child_index).to_be_less_than(overlap_result.composition.batches.len() - 1)
expect(_iframe_pixels(overlap_result, 80, 50)[20 + 20 * 80]).to_equal(0xFFEF4444u32)
for batch in basic.composition.batches:
    if batch.embedding.component_id.contains("iframe"):
        for command in batch.commands:
            expect(command.clip_rect.present).to_equal(true)
            expect(batch.embedding.layer).to_equal(0)
val clipped = "<html><body style='margin:0;background-color:#ffffff'><div style='width:20px;height:15px;overflow:hidden'><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\"></iframe></div></body></html>"
val clipped_pixels = _iframe_pixels(
    simple_web_layout_render_html_draw_ir_result(clipped, 60, 40),
    60, 40
)
expect(clipped_pixels[10 + 5 * 60]).to_equal(0xFF22C55Eu32)
expect(clipped_pixels[25 + 5 * 60]).to_equal(0xFFFFFFFFu32)

step("Bound nested iframe work and fail closed")
val orange = "<body style='margin:0;background-color:#f97316'></body>"
val nested = "<body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"" + _iframe_escape(orange) + "\"></iframe></body>"
val nested_html = "<html><body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"" + _iframe_escape(nested) + "\"></iframe></body></html>"
expect(_iframe_pixels(simple_web_layout_render_html_draw_ir_result(nested_html, 40, 30), 40, 30)[5 + 5 * 40]).to_equal(0xFFF97316u32)
val depth4 = "<body style='margin:0;background-color:#3b82f6'></body>"
var capped = depth4
var level = 0
while level < 4:
    capped = "<body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"" + _iframe_escape(capped) + "\"></iframe></body>"
    level = level + 1
expect(_iframe_pixels(simple_web_layout_render_html_draw_ir_result(capped, 40, 30), 40, 30)[5 + 5 * 40]).to_equal(0xFF888888u32)
val fractional = "<html><body style='margin:0'><div style='opacity:0.5'><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\"></iframe></div></body></html>"
expect(_iframe_has_placeholder(
    simple_web_layout_render_html_draw_ir_result(fractional, 40, 30).composition
)).to_equal(true)
val fractional_overlap = "<html><body style='margin:0;background-color:#ffffff'><div style='position:relative;width:40px;height:30px;opacity:0.5'><div style='position:absolute;left:0;top:0;width:40px;height:30px;background-color:#000000'></div><iframe width='40' height='30' style='position:absolute;left:0;top:0' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\"></iframe><div style='position:absolute;left:30px;top:0;width:10px;height:30px;background-color:#ef4444'></div></div></body></html>"
val fractional_result = simple_web_layout_render_html_draw_ir_result(
    fractional_overlap, 40, 30
)
expect(_iframe_opacity_batch_count(fractional_result.composition)).to_equal(1)
val fractional_pixels = _iframe_pixels(fractional_result, 40, 30)
# Canonical composite contract (a8 = 500*255/1000 = 127; out =
# (src*a8 + dst*(256-a8)) >> 8, see engine2d_composite_region_milli):
# #888 over white -> (136*127+255*129)>>8 = 195 = #c3c3c3; #ef4444
# over white -> r 247, g/b (68*127+255*129)>>8 = 162 = #f7a2a2. A
# separately composited placeholder would blend a second time and
# fail these exact pixels.
expect(fractional_pixels[10 + 10 * 40]).to_equal(0xFFC3C3C3u32)
expect(fractional_pixels[35 + 10 * 40]).to_equal(0xFFF7A2A2u32)

step("Retire legacy iframe pixel blitting after parity")
expect(_iframe_has_image_or_material_or_hit(basic.composition)).to_equal(false)
val inert_child = "<html><body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;script&gt;fetch('https://invalid.example/')&lt;/script&gt;&lt;img src='https://invalid.example/x.png'&gt;&lt;input value='blocked'&gt;&lt;/body&gt;\"></iframe></body></html>"
val inert_result = simple_web_layout_render_html_draw_ir_result(
    inert_child, 40, 30
)
expect(_iframe_pixels(inert_result, 40, 30)[5 + 5 * 40]).to_equal(0xFF22C55Eu32)
expect(_iframe_has_image_or_material_or_hit(inert_result.composition)).to_equal(false)
val child_scroll_reset = "<html><body style='margin:0'><iframe width='40' height='30' style='display:block' srcdoc=\"&lt;body style='margin:0'&gt;&lt;div style='width:40px;height:15px;background-color:#ef4444'&gt;&lt;/div&gt;&lt;div style='width:40px;height:15px;background-color:#22c55e'&gt;&lt;/div&gt;&lt;/body&gt;\"></iframe></body></html>"
val child_scroll_pixels = _iframe_pixels(
    simple_web_layout_render_html_draw_ir_result(child_scroll_reset, 40, 30),
    40, 30
)
expect(child_scroll_pixels[5 + 5 * 40]).to_equal(0xFFEF4444u32)
expect(child_scroll_pixels[5 + 20 * 40]).to_equal(0xFF22C55Eu32)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `971f384b3ed3c81737d8e6c2c65f0275352569ae86f8bc4c9d6b2f3d752f605b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `971f384b3ed3c81737d8e6c2c65f0275352569ae86f8bc4c9d6b2f3d752f605b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `971f384b3ed3c81737d8e6c2c65f0275352569ae86f8bc4c9d6b2f3d752f605b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl
mirror: doc/06_spec/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps iframe embedding canonical and fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
