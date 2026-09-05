# Simple Web Engine Budget + Quota Hardening Specification

> Guards the hostile-page hardening added to the pure-Simple HTML/CSS software renderer (`simple_web_html_layout_renderer.spl`): a monotonic render budget and CSS rule/declaration quotas that degrade GRACEFULLY (return a correctly sized, partially painted framebuffer) instead of hanging, plus the `body`/`html` canvas background-color propagation to the full viewport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine Budget + Quota Hardening Specification

Guards the hostile-page hardening added to the pure-Simple HTML/CSS software renderer (`simple_web_html_layout_renderer.spl`): a monotonic render budget and CSS rule/declaration quotas that degrade GRACEFULLY (return a correctly sized, partially painted framebuffer) instead of hanging, plus the `body`/`html` canvas background-color propagation to the full viewport.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Guards the hostile-page hardening added to the pure-Simple HTML/CSS software
renderer (`simple_web_html_layout_renderer.spl`): a monotonic render budget and
CSS rule/declaration quotas that degrade GRACEFULLY (return a correctly sized,
partially painted framebuffer) instead of hanging, plus the `body`/`html` canvas
background-color propagation to the full viewport.

Absolute oracles only: exact framebuffer length (`width * height`), exact pixel
colors, and the honest degraded flag. The render budget is exercised via the
overridable `budget_ms` parameter so a hostile sheet trips deterministically in
milliseconds rather than waiting out the 10s default.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### Simple Web engine budget + quota hardening

#### returns a full-sized degraded framebuffer when the budget trips on an oversized stylesheet

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a full-sized degraded framebuffer when the budget trips on an oversized stylesheet
- Render a ~45KB generated stylesheet at 96x64 under a generous 60s budget
- Assert it completes: framebuffer length is exactly width*height and it is NOT degraded
   - Expected: ok.len() equals `W * H`
   - Expected: simple_web_layout_last_render_degraded() is false
- Render the same page under a 1ms budget so a phase must stop early
- Assert graceful degradation: still a full-sized buffer, and the flag honestly reports the trip
   - Expected: degraded.len() equals `W * H`
   - Expected: simple_web_layout_last_render_degraded() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a full-sized degraded framebuffer when the budget trips on an oversized stylesheet")
step("Render a ~45KB generated stylesheet at 96x64 under a generous 60s budget")
val html = "<html><head>" + _oversized_style(1500) + "</head><body class=\"g0 g1\"><div class=\"g2\">hi</div></body></html>"
# Generous budget so this completion assertion is not load-sensitive; the
# 1ms call below is the actual degradation test.
val ok = simple_web_layout_render_html_software_pixels(html, W, H, 60000)
step("Assert it completes: framebuffer length is exactly width*height and it is NOT degraded")
expect(ok.len()).to_equal(W * H)
expect(simple_web_layout_last_render_degraded()).to_equal(false)
step("Render the same page under a 1ms budget so a phase must stop early")
val degraded = simple_web_layout_render_html_software_pixels(html, W, H, 1)
step("Assert graceful degradation: still a full-sized buffer, and the flag honestly reports the trip")
expect(degraded.len()).to_equal(W * H)
expect(simple_web_layout_last_render_degraded()).to_equal(true)
```

</details>

#### carries the degraded verdict onto the readback result so font evidence can fail closed

- carries the degraded verdict onto the readback result so font evidence can fail closed
- Render a page whose text node carries an explicit non-default font, under the default budget
- Assert a completed render reports render_degraded=false and publishes a non-empty font identity
   - Expected: complete.render_degraded is false
   - Expected: complete.vector_font_identity == "" is false
- Assert the completed render resolved the DECLARED font size, not the 16px CSS default
   - Expected: complete.vector_font_pixel_size equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries the degraded verdict onto the readback result so font evidence can fail closed")
# Regression guard for
# doc/08_tracking/bug/web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01.md
# The style cascade breaks on budget expiry and leaves unreached nodes on
# renderer_default_style() (sans-serif/16px). Before this field existed the
# readback result still published vector_font_* as if it were complete
# evidence, so a TRUNCATED render was indistinguishable from a genuine font
# mismatch. The verdict must travel WITH the result, not just in a global.
val html = "<html><body><p style=\"font-family: Bungee; font-size: 100px\">Hi</p></body></html>"
step("Render a page whose text node carries an explicit non-default font, under the default budget")
val complete = simple_web_layout_render_html_readback_engine2d_result(html, W, H, "software")
step("Assert a completed render reports render_degraded=false and publishes a non-empty font identity")
expect(complete.render_degraded).to_equal(false)
expect(complete.vector_font_identity == "").to_equal(false)
step("Assert the completed render resolved the DECLARED font size, not the 16px CSS default")
expect(complete.vector_font_pixel_size).to_equal(100)
```

</details>

#### keeps the first stylesheet rule effective when total rules exceed the quota

- keeps the first stylesheet rule effective when total rules exceed the quota
- Render body background #3050a0 followed by 4300 distinct junk rules (over the 4096 quota)
- Assert render completes at exact size and is not degraded
   - Expected: pixels.len() equals `W * H`
   - Expected: simple_web_layout_last_render_degraded() is false
- Assert a background pixel equals the first rule's color exactly
   - Expected: _px(pixels, 4, 58) equals `0xFF3050A0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the first stylesheet rule effective when total rules exceed the quota")
step("Render body background #3050a0 followed by 4300 distinct junk rules (over the 4096 quota)")
val html = "<html><head>" + _quota_style(4300) + "</head><body></body></html>"
# Generous budget: this scenario's intent is the RULE QUOTA, so keep the
# monotonic budget out of its way (the parse of 4300 rules is O(rules)).
val pixels = simple_web_layout_render_html_software_pixels(html, W, H, 60000)
step("Assert render completes at exact size and is not degraded")
expect(pixels.len()).to_equal(W * H)
expect(simple_web_layout_last_render_degraded()).to_equal(false)
step("Assert a background pixel equals the first rule's color exactly")
expect(_px(pixels, 4, 58)).to_equal(0xFF3050A0u32)
```

</details>

#### renders a small honest page exactly and reports it as not degraded

- renders a small honest page exactly and reports it as not degraded
- Render a 40x30 green block on an unstyled body at 96x64
- Assert the block's center pixel is exactly the block color and the render is not degraded
   - Expected: pixels.len() equals `W * H`
   - Expected: _px(pixels, 20, 15) equals `0xFF20C040u32`
   - Expected: simple_web_layout_last_render_degraded() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a small honest page exactly and reports it as not degraded")
step("Render a 40x30 green block on an unstyled body at 96x64")
val html = "<html><body style=\"margin:0\"><div style=\"width:40px;height:30px;background:#20c040\"></div></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, W, H)
step("Assert the block's center pixel is exactly the block color and the render is not degraded")
expect(pixels.len()).to_equal(W * H)
expect(_px(pixels, 20, 15)).to_equal(0xFF20C040u32)
expect(simple_web_layout_last_render_degraded()).to_equal(false)
```

</details>

#### propagates the body background to the viewport below the content

- propagates the body background to the viewport below the content
- Render body background #204060 with a 96x20 header block #d04030 at 96x64
- Assert a pixel inside the header equals the header color exactly
   - Expected: _px(pixels, 48, 10) equals `0xFFD04030u32`
- Assert a pixel well below the content equals the body background color exactly
   - Expected: _px(pixels, 48, 45) equals `0xFF204060u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates the body background to the viewport below the content")
step("Render body background #204060 with a 96x20 header block #d04030 at 96x64")
val html = "<html><body style=\"margin:0;background:#204060\"><div style=\"width:96px;height:20px;background:#d04030\"></div></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, W, H)
step("Assert a pixel inside the header equals the header color exactly")
expect(_px(pixels, 48, 10)).to_equal(0xFFD04030u32)
step("Assert a pixel well below the content equals the body background color exactly")
expect(_px(pixels, 48, 45)).to_equal(0xFF204060u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3804e54d4b29353d96e65cfec7486a0bd7f7c94e9a9bed3aacaa4e37bda58238`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3804e54d4b29353d96e65cfec7486a0bd7f7c94e9a9bed3aacaa4e37bda58238`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3804e54d4b29353d96e65cfec7486a0bd7f7c94e9a9bed3aacaa4e37bda58238`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a full-sized degraded framebuffer when the budget trips on an oversized stylesheet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the degraded verdict onto the readback result so font evidence can fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the first stylesheet rule effective when total rules exceed the quota' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
