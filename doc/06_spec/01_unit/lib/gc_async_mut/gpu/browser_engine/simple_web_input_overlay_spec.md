# Simple Web Input Overlay Specification

> Tests covering Simple web input overlay.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Input Overlay Specification

## Scenarios

### Simple web input overlay

#### emits clipped selection before canonical text and clipped caret after it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits clipped selection before canonical text and clipped caret after it
   - Expected: collapsed_commands[caret_index].color equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits clipped selection before canonical text and clipped caret after it")
val html = "<style>html,body{{margin:0}}#q{width:80px;height:18px;padding:2px;color:#111827;caret-color:#ef4444}</style><input id='q' value='abc'>"
val selected = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 30, 0, _overlay("path:0", 0, 2, 0, false)
)
val selected_commands = selected.composition.batches[0].commands
val selection_index = _command_index(selected_commands, "q_selection")
val text_index = _command_index(selected_commands, "q_value")
expect(selection_index).to_be_greater_than(-1)
expect(text_index).to_be_greater_than(selection_index)
expect(selected_commands[selection_index].clip_rect.present).to_be(true)

val collapsed = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 30, 0, _overlay("path:0", 2, 2, 0, true)
)
val collapsed_commands = collapsed.composition.batches[0].commands
val collapsed_text_index = _command_index(collapsed_commands, "q_value")
val caret_index = _command_index(collapsed_commands, "q_caret")
expect(caret_index).to_be_greater_than(collapsed_text_index)
expect(collapsed_commands[caret_index].color).to_equal(0xFFEF4444u32)
expect(collapsed_commands[caret_index].clip_rect.present).to_be(true)
```

</details>

#### derives selection RGB from CSS caret color with fixed named alpha

- derives selection RGB from CSS caret color with fixed named alpha
   - Expected: red_color equals `0x66EF4444u32`
   - Expected: green_color equals `0x6622C55Eu32`
   - Expected: (red_color >> 24) & 0xFFu32 equals `0x66u32`
   - Expected: (green_color >> 24) & 0xFFu32 equals `0x66u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives selection RGB from CSS caret color with fixed named alpha")
val red = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    "<style>#q{width:80px;height:18px;caret-color:#ef4444}</style><input id='q' value='abc'>",
    100, 30, 0, _overlay("path:0", 0, 2, 0, false)
)
val green = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    "<style>#q{width:80px;height:18px;color:#22c55e}</style><input id='q' value='abc'>",
    100, 30, 0, _overlay("path:0", 0, 2, 0, false)
)
val red_commands = red.composition.batches[0].commands
val green_commands = green.composition.batches[0].commands
val red_color = red_commands[
    _command_index(red_commands, "q_selection")
].color
val green_color = green_commands[
    _command_index(green_commands, "q_selection")
].color
expect(red_color).to_equal(0x66EF4444u32)
expect(green_color).to_equal(0x6622C55Eu32)
expect(red_color).not.to_equal(green_color)
expect((red_color >> 24) & 0xFFu32).to_equal(0x66u32)
expect((green_color >> 24) & 0xFFu32).to_equal(0x66u32)
```

</details>

#### keeps password cleartext out while preserving UTF-8 source boundaries

- keeps password cleartext out while preserving UTF-8 source boundaries
   - Expected: commands[text_index].text_value equals `**`
   - Expected: hit.source_boundary_bytes.len() equals `3`
   - Expected: hit.source_boundary_bytes[0] equals `0`
   - Expected: hit.source_boundary_bytes[1] equals `2`
   - Expected: hit.source_boundary_bytes[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps password cleartext out while preserving UTF-8 source boundaries")
val html = "<style>html,body{{margin:0}}#secret{width:80px;height:18px}</style><input id='secret' type='password' value='éx'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 30, 0, _overlay("path:0", 2, 2, 0, true)
)
val commands = result.composition.batches[0].commands
val text_index = _command_index(commands, "secret_value")
val hit = _input_hit(result.hit_index.input_text_hits, "path:0")
expect(commands[text_index].text_value).to_equal("**")
expect(commands[text_index].text_value).not.to_contain("é")
expect(hit.source_boundary_bytes.len()).to_equal(3)
expect(hit.source_boundary_bytes[0]).to_equal(0)
expect(hit.source_boundary_bytes[1]).to_equal(2)
expect(hit.source_boundary_bytes[2]).to_equal(3)
```

</details>

#### maps uppercase expansion to source scalar boundaries

- maps uppercase expansion to source scalar boundaries
   - Expected: commands[_command_index(commands, "q_value")].text_value equals `SSA`
   - Expected: hit.source_boundary_bytes.len() equals `3`
   - Expected: hit.source_boundary_bytes[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps uppercase expansion to source scalar boundaries")
val html = "<style>html,body{{margin:0}}#q{width:100px;height:18px;text-transform:uppercase}</style><input id='q' value='ßa'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 120, 30, 0, _overlay("path:0", 2, 2, 0, true)
)
val commands = result.composition.batches[0].commands
val hit = _input_hit(result.hit_index.input_text_hits, "path:0")
expect(commands[_command_index(commands, "q_value")].text_value).to_equal("SSA")
expect(hit.source_boundary_bytes.len()).to_equal(3)
expect(hit.source_boundary_bytes[1]).to_equal(2)
expect(hit.boundary_x_px[1]).to_be_greater_than(hit.boundary_x_px[0])
```

</details>

#### maps RTL source boundaries to descending visual x

- maps RTL source boundaries to descending visual x


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps RTL source boundaries to descending visual x")
val html = "<style>html,body{{margin:0}}#q{width:80px;height:18px;direction:rtl}</style><input id='q' value='abé'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 30, 0, _overlay("path:0", 0, 0, 0, true)
)
val hit = _input_hit(result.hit_index.input_text_hits, "path:0")
expect(hit.boundary_x_px[0]).to_be_greater_than(hit.boundary_x_px[1])
expect(hit.boundary_x_px[1]).to_be_greater_than(hit.boundary_x_px[2])
expect(hit.boundary_x_px[2]).to_be_greater_than(hit.boundary_x_px[3])
```

</details>

#### omits disabled controls from overlay hit geometry

- omits disabled controls from overlay hit geometry
   - Expected: result.hit_index.input_text_hits.len() equals `0`
   - Expected: followed.hit_index.input_text_hits.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("omits disabled controls from overlay hit geometry")
val html = "<style>html,body{{margin:0}}#q{width:80px;height:18px}</style><input id='q' value='abc' disabled>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 30, 0, _overlay("path:0", 1, 1, 0, true)
)
expect(result.hit_index.input_text_hits.len()).to_equal(0)
expect(_command_index(
    result.composition.batches[0].commands, "q_caret"
)).to_equal(-1)

val followed = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    "<style>#q{width:80px;height:18px}</style><input disabled class='x' id='q' value='abc'>",
    100, 30, 0, _overlay("path:0", 0, 2, 0, true)
)
val followed_commands = followed.composition.batches[0].commands
expect(followed.hit_index.input_text_hits.len()).to_equal(0)
expect(_command_index(
    followed_commands, "q_selection"
)).to_equal(-1)
expect(_command_index(
    followed_commands, "q_caret"
)).to_equal(-1)
```

</details>

#### fails closed on malformed and truncated raw input values

- fails closed on malformed and truncated raw input values
   - Expected: invalid.hit_index.input_text_hits.len() equals `0`
   - Expected: _command_index(invalid_commands, "q_value") equals `-1`
   - Expected: _command_index(invalid_commands, "q_caret") equals `-1`
   - Expected: truncated_result.hit_index.input_text_hits.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on malformed and truncated raw input values")
val invalid_continuation = rt_bytes_to_text([
    0xE2u8, 0x28u8, 0xA1u8
])
val truncated = rt_bytes_to_text([0xE2u8, 0x82u8])
expect(text_is_valid_utf8(invalid_continuation)).to_be(false)
expect(text_is_valid_utf8(truncated)).to_be(false)
val invalid = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    "<input id='q' value='" + invalid_continuation + "'>",
    100, 30, 0, _overlay("path:0", 0, 0, 0, true)
)
val invalid_commands = invalid.composition.batches[0].commands
expect(invalid.hit_index.input_text_hits.len()).to_equal(0)
expect(_command_index(invalid_commands, "q_value")).to_equal(-1)
expect(_command_index(invalid_commands, "q_caret")).to_equal(-1)

val truncated_result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    "<input id='q' value='" + truncated + "'>",
    100, 30, 0, _overlay("path:0", 0, 0, 0, true)
)
val truncated_commands = (
    truncated_result.composition.batches[0].commands
)
expect(truncated_result.hit_index.input_text_hits.len()).to_equal(0)
expect(_command_index(
    truncated_commands, "q_value"
)).to_equal(-1)
expect(_command_index(
    truncated_commands, "q_caret"
)).to_equal(-1)
```

</details>

#### reveals a long suffix without splitting a source scalar

- reveals a long suffix without splitting a source scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reveals a long suffix without splitting a source scalar")
val html = "<style>html,body{{margin:0}}#q{width:24px;height:18px;padding:1px}</style><input id='q' value='abcdeéfghij'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 50, 30, 0, _overlay("path:0", 12, 12, 0, true)
)
val hit = _input_hit(result.hit_index.input_text_hits, "path:0")
expect(result.resolved_input_view_start_byte).to_be_greater_than(0)
expect(hit.source_boundary_bytes).to_contain(
    result.resolved_input_view_start_byte
)
```

</details>

#### clips CPU Draw IR overlay pixels and restores following commands

- clips CPU Draw IR overlay pixels and restores following commands
   - Expected: pixels.len() equals `1500`
   - Expected: pixels[49] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips CPU Draw IR overlay pixels and restores following commands")
val html = "<style>html,body{margin:0;background:#fff}#q{width:24px;height:18px;padding:1px;caret-color:#3b82f6}</style><input id='q' value='abcdef'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 50, 30, 0, _overlay("path:0", 0, 4, 0, false)
)
val pixels = simple_web_render_draw_ir_composition_with_cpu_backend(
    result.composition, 50, 30
)
expect(pixels.len()).to_equal(1500)
expect(pixels).to_contain(0x663B82F6u32)
expect(pixels[49]).to_equal(0xFFFFFFFFu32)
```

</details>

#### keeps duplicate author IDs distinct through canonical path keys

- keeps duplicate author IDs distinct through canonical path keys
   - Expected: hits.len() equals `2`
   - Expected: hits[0].target_key equals `path:0`
   - Expected: hits[1].target_key equals `path:1`
   - Expected: selection.clip_rect.y equals `hits[1].y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps duplicate author IDs distinct through canonical path keys")
val html = "<style>html,body{{margin:0}}input{display:block;width:80px;height:18px}</style><input id='dup' value='first'><input id='dup' value='second'>"
val result = simple_web_layout_render_html_draw_ir_result_with_overlay_at_time(
    html, 100, 50, 0, _overlay("path:1", 0, 3, 0, false)
)
val hits = result.hit_index.input_text_hits
expect(hits.len()).to_equal(2)
expect(hits[0].target_key).to_equal("path:0")
expect(hits[1].target_key).to_equal("path:1")
expect(simple_web_layout_hit_test_index(
    result.hit_index, hits[0].x + 1, hits[0].y + 1
)).to_equal("path:0")
expect(simple_web_layout_hit_test_index(
    result.hit_index, hits[1].x + 1, hits[1].y + 1
)).to_equal("path:1")
val commands = result.composition.batches[0].commands
val selection_index = _command_index(commands, "dup_selection")
expect(selection_index).to_be_greater_than(-1)
val selection = commands[selection_index]
expect(selection.clip_rect.y).to_equal(hits[1].y)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple web input overlay.
- Simple web input overlay

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `78c5c16302dd83992ae1a8f97515890b221d4c00446205a68b135c70bf2be70d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78c5c16302dd83992ae1a8f97515890b221d4c00446205a68b135c70bf2be70d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78c5c16302dd83992ae1a8f97515890b221d4c00446205a68b135c70bf2be70d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits clipped selection before canonical text and clipped caret after it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives selection RGB from CSS caret color with fixed named alpha' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps password cleartext out while preserving UTF-8 source boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
