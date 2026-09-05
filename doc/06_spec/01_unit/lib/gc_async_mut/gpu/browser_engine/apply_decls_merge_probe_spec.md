# apply_decls_merge_probe_spec

> Every case here uses only properties from _APPLY_DECLS_DISPATCH_PROPS

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# apply_decls_merge_probe_spec

Every case here uses only properties from _APPLY_DECLS_DISPATCH_PROPS

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Every case here uses only properties from _APPLY_DECLS_DISPATCH_PROPS
    (box-sizing, color, width, height, min-height, margin-left, z-index,
    display) so it exercises the new dispatch path. Each is paired with an
    equivalent case that adds one property NOT in that list (an "obscure"
    one -- letter-spacing, unrelated to anything tested here) to force the
    same node through the pre-existing full-probe fallback instead. The
    two paths must produce identical results for the shared properties.

## Scenarios

### apply_decls per-node merge preserves cascade semantics

#### last-wins for the same property across two rules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- last-wins for the same property across two rules
   - Expected: simple_web_layout_debug_style_by_id(html, "t1", "font_size") equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last-wins for the same property across two rules")
val html = "<html><head><style>#t1{font-size:12px;}#t1{font-size:24px;}</style></head><body><div id=\"t1\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "t1", "font_size")).to_equal("24")
```

</details>

#### shorthand after longhand wins (background resets background-color)

- shorthand after longhand wins (background resets background-color)
   - Expected: simple_web_layout_debug_style_by_id(html, "t2", "background_color") equals `4278190335`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shorthand after longhand wins (background resets background-color)")
# ARGB u32 encoding (confirmed via the passing case below): opaque
# red = 0xFFFF0000 = 4294901760, opaque blue = 0xFF0000FF = 4278190335.
val html = "<html><head><style>#t2{background-color:#ff0000;}#t2{background:#0000ff;}</style></head><body><div id=\"t2\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "t2", "background_color")).to_equal("4278190335")
```

</details>

#### longhand after shorthand wins (background-color overrides background)

- longhand after shorthand wins (background-color overrides background)
   - Expected: simple_web_layout_debug_style_by_id(html, "t3", "background_color") equals `4294901760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("longhand after shorthand wins (background-color overrides background)")
val html = "<html><head><style>#t3{background:#0000ff;}#t3{background-color:#ff0000;}</style></head><body><div id=\"t3\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "t3", "background_color")).to_equal("4294901760")
```

</details>

#### cascade across 3 rules with non-ASCII content elsewhere is not corrupted

- cascade across 3 rules with non-ASCII content elsewhere is not corrupted
   - Expected: simple_web_layout_debug_style_by_id(html, "t4", "font_size") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cascade across 3 rules with non-ASCII content elsewhere is not corrupted")
val html = "<html><head><style>.café{font-size:10px;}.日本語{font-size:15px;}#t4{font-size:20px;}</style></head><body><div id=\"t4\" class=\"café 日本語\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "t4", "font_size")).to_equal("20")
```

</details>

#### many candidate rules still merge correctly (order preserved past several)

- many candidate rules still merge correctly (order preserved past several)
   - Expected: simple_web_layout_debug_style_by_id(html, "t5", "font_size") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("many candidate rules still merge correctly (order preserved past several)")
val html = "<html><head><style>.a{font-size:1px;}.b{font-size:2px;}.c{font-size:3px;}.d{font-size:4px;}#t5{font-size:5px;}</style></head><body><div id=\"t5\" class=\"a b c d\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "t5", "font_size")).to_equal("5")
```

</details>

### apply_decls stage-1 dispatch/probe-fallback equivalence

#### dispatch path: width/height/margin-left/box-sizing apply correctly

- dispatch path: width/height/margin-left/box-sizing apply correctly
   - Expected: simple_web_layout_debug_style_by_id(html, "d1", "width") equals `150`
   - Expected: simple_web_layout_debug_style_by_id(html, "d1", "height") equals `80`
   - Expected: simple_web_layout_debug_style_by_id(html, "d1", "margin_l") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: width/height/margin-left/box-sizing apply correctly")
# All four properties are in _APPLY_DECLS_DISPATCH_PROPS, so this
# call takes the dispatch path (verified via the equivalent
# fallback-forced case below producing the same result).
val html = "<html><head><style>#d1{box-sizing:border-box;width:150px;height:80px;margin-left:20px;}</style></head><body><div id=\"d1\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d1", "width")).to_equal("150")
expect(simple_web_layout_debug_style_by_id(html, "d1", "height")).to_equal("80")
expect(simple_web_layout_debug_style_by_id(html, "d1", "margin_l")).to_equal("20")
```

</details>

#### fallback path: identical width/height/margin-left plus one unhandled property give the same result

- fallback path: identical width/height/margin-left plus one unhandled property give the same result
   - Expected: simple_web_layout_debug_style_by_id(html, "d2", "width") equals `150`
   - Expected: simple_web_layout_debug_style_by_id(html, "d2", "height") equals `80`
   - Expected: simple_web_layout_debug_style_by_id(html, "d2", "margin_l") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: identical width/height/margin-left plus one unhandled property give the same result")
# letter-spacing is not in _APPLY_DECLS_DISPATCH_PROPS, so this decl
# block forces the pre-existing full-probe path for the whole call.
# ("background" is also not in the dispatch list, so it is omitted
# here -- this isolates the dispatch-handled properties.)
val html = "<html><head><style>#d2{width:150px;height:80px;margin-left:20px;letter-spacing:1px;}</style></head><body><div id=\"d2\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d2", "width")).to_equal("150")
expect(simple_web_layout_debug_style_by_id(html, "d2", "height")).to_equal("80")
expect(simple_web_layout_debug_style_by_id(html, "d2", "margin_l")).to_equal("20")
```

</details>

#### dispatch path: margin-left auto

- dispatch path: margin-left auto
   - Expected: simple_web_layout_debug_style_by_id(html, "d3", "margin_l") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: margin-left auto")
val html = "<html><head><style>#d3{margin-left:auto;}</style></head><body><div id=\"d3\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d3", "margin_l")).to_equal("0")
```

</details>

#### dispatch path: display:contents resets width/margin-left to 0 regardless of other decls in the same call

- dispatch path: display:contents resets width/margin-left to 0 regardless of other decls in the same call
   - Expected: simple_web_layout_debug_style_by_id(html, "d4", "display") equals `contents`
   - Expected: simple_web_layout_debug_style_by_id(html, "d4", "width") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "d4", "margin_l") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: display:contents resets width/margin-left to 0 regardless of other decls in the same call")
val html = "<html><head><style>#d4{display:contents;width:300px;margin-left:40px;}</style></head><body><div id=\"d4\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d4", "display")).to_equal("contents")
expect(simple_web_layout_debug_style_by_id(html, "d4", "width")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "d4", "margin_l")).to_equal("0")
```

</details>

#### fallback path: display:contents reset still applies when an unhandled property forces fallback

- fallback path: display:contents reset still applies when an unhandled property forces fallback
   - Expected: simple_web_layout_debug_style_by_id(html, "d5", "display") equals `contents`
   - Expected: simple_web_layout_debug_style_by_id(html, "d5", "width") equals `0`
   - Expected: simple_web_layout_debug_style_by_id(html, "d5", "margin_l") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: display:contents reset still applies when an unhandled property forces fallback")
# border-left is a stage-2 dispatch candidate that was deliberately
# deferred (see the bug doc), so it still forces fallback here.
val html = "<html><head><style>#d5{display:contents;width:300px;margin-left:40px;border-left:2px solid #000;}</style></head><body><div id=\"d5\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d5", "display")).to_equal("contents")
expect(simple_web_layout_debug_style_by_id(html, "d5", "width")).to_equal("0")
expect(simple_web_layout_debug_style_by_id(html, "d5", "margin_l")).to_equal("0")
```

</details>

#### dispatch path: width percentage and vw sentinel forms

- dispatch path: width percentage and vw sentinel forms
   - Expected: simple_web_layout_debug_style_by_id(html, "d6", "width") equals `-50`
   - Expected: simple_web_layout_debug_style_by_id(html, "d7", "width") equals `-10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: width percentage and vw sentinel forms")
val html = "<html><head><style>#d6{width:50%;}#d7{width:10vw;}</style></head><body><div id=\"d6\">x</div><div id=\"d7\">y</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "d6", "width")).to_equal("-50")
expect(simple_web_layout_debug_style_by_id(html, "d7", "width")).to_equal("-10")
```

</details>

### apply_decls stage-2 dispatch/probe-fallback equivalence

#### dispatch path: margin shorthand alone (all four sides from one token)

- dispatch path: margin shorthand alone (all four sides from one token)
   - Expected: simple_web_layout_debug_style_by_id(html, "e1", "margin_l") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: margin shorthand alone (all four sides from one token)")
val html = "<html><head><style>#e1{margin:15px;}</style></head><body><div id=\"e1\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e1", "margin_l")).to_equal("15")
```

</details>

#### dispatch path: margin shorthand followed by margin-left longhand (longhand wins, later in source order)

- dispatch path: margin shorthand followed by margin-left longhand (longhand wins, later in source order)
   - Expected: simple_web_layout_debug_style_by_id(html, "e2", "margin_l") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: margin shorthand followed by margin-left longhand (longhand wins, later in source order)")
val html = "<html><head><style>#e2{margin:15px;margin-left:40px;}</style></head><body><div id=\"e2\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e2", "margin_l")).to_equal("40")
```

</details>

#### fallback path: identical margin+margin-left plus one unhandled property give the same result

- fallback path: identical margin+margin-left plus one unhandled property give the same result
   - Expected: simple_web_layout_debug_style_by_id(html, "e3", "margin_l") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: identical margin+margin-left plus one unhandled property give the same result")
val html = "<html><head><style>#e3{margin:15px;margin-left:40px;border-left:2px solid #000;}</style></head><body><div id=\"e3\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e3", "margin_l")).to_equal("40")
```

</details>

#### dispatch path: margin-left BEFORE margin in source order has margin (shorthand) win -- standard source-order cascade

- dispatch path: margin-left BEFORE margin in source order has margin (shorthand) win -- standard source-order cascade
   - Expected: simple_web_layout_debug_style_by_id(html, "e4", "margin_l") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: margin-left BEFORE margin in source order has margin (shorthand) win -- standard source-order cascade")
# This used to pin a non-standard "fixed code order" behavior where
# margin-left always won regardless of source position (see
# "Pre-existing non-standard margin/margin-left ordering" in the bug
# doc, filed 2026-07-29). That has since been fixed: both the
# full-probe body (simple_web_html_layout_renderer_decl_apply.spl,
# around the "Cascade order within the margin family" comment) and
# the dispatch path (simple_web_html_layout_renderer_declarations.spl,
# around the "Cascade order for the margin family mirrors the
# full-probe body" comment) now compare decl_tbl source positions via
# decl_tbl_last_index, so the LAST declaration in source order wins
# per side -- standard CSS cascade semantics. Here margin-left(40)
# appears before margin(15) in source, so the margin shorthand
# (later, and it resets margin-left too) wins: margin_l is 15.
val html = "<html><head><style>#e4{margin-left:40px;margin:15px;}</style></head><body><div id=\"e4\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e4", "margin_l")).to_equal("15")
```

</details>

#### fallback path: same margin-left-before-margin case plus one unhandled property gives the same result

- fallback path: same margin-left-before-margin case plus one unhandled property gives the same result
   - Expected: simple_web_layout_debug_style_by_id(html, "e5", "margin_l") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: same margin-left-before-margin case plus one unhandled property gives the same result")
val html = "<html><head><style>#e5{margin-left:40px;margin:15px;border-left:2px solid #000;}</style></head><body><div id=\"e5\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e5", "margin_l")).to_equal("15")
```

</details>

#### dispatch path: padding shorthand expands to all four sides with 2-value form

- dispatch path: padding shorthand expands to all four sides with 2-value form
   - Expected: simple_web_layout_debug_style_by_id(html, "e6", "pad_l") equals `20`
   - Expected: simple_web_layout_debug_style_by_id(html, "e6", "pad_r") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: padding shorthand expands to all four sides with 2-value form")
val html = "<html><head><style>#e6{padding:10px 20px;}</style></head><body><div id=\"e6\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e6", "pad_l")).to_equal("20")
expect(simple_web_layout_debug_style_by_id(html, "e6", "pad_r")).to_equal("20")
```

</details>

#### fallback path: identical padding plus one unhandled property gives the same result

- fallback path: identical padding plus one unhandled property gives the same result
   - Expected: simple_web_layout_debug_style_by_id(html, "e7", "pad_l") equals `20`
   - Expected: simple_web_layout_debug_style_by_id(html, "e7", "pad_r") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: identical padding plus one unhandled property gives the same result")
val html = "<html><head><style>#e7{padding:10px 20px;border-left:2px solid #000;}</style></head><body><div id=\"e7\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e7", "pad_l")).to_equal("20")
expect(simple_web_layout_debug_style_by_id(html, "e7", "pad_r")).to_equal("20")
```

</details>

#### dispatch path: the full stage-2 property set together does not corrupt unrelated width/height/margin_l

- dispatch path: the full stage-2 property set together does not corrupt unrelated width/height/margin_l
   - Expected: simple_web_layout_debug_style_by_id(html, "e8", "width") equals `90`
   - Expected: simple_web_layout_debug_style_by_id(html, "e8", "height") equals `40`
   - Expected: simple_web_layout_debug_style_by_id(html, "e8", "margin_l") equals `10`
   - Expected: simple_web_layout_debug_style_by_id(html, "e8", "pad_l") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch path: the full stage-2 property set together does not corrupt unrelated width/height/margin_l")
val html = "<html><head><style>#e8{justify-content:center;align-items:center;gap:8px;text-align:left;cursor:pointer;outline:2px solid #000;overflow:hidden;box-shadow:0 2px 4px #000;padding:5px;margin:10px;width:90px;height:40px;}</style></head><body><div id=\"e8\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e8", "width")).to_equal("90")
expect(simple_web_layout_debug_style_by_id(html, "e8", "height")).to_equal("40")
expect(simple_web_layout_debug_style_by_id(html, "e8", "margin_l")).to_equal("10")
expect(simple_web_layout_debug_style_by_id(html, "e8", "pad_l")).to_equal("5")
```

</details>

#### fallback path: the same full stage-2 property set plus one unhandled property gives the same result

- fallback path: the same full stage-2 property set plus one unhandled property gives the same result
   - Expected: simple_web_layout_debug_style_by_id(html, "e9", "width") equals `90`
   - Expected: simple_web_layout_debug_style_by_id(html, "e9", "height") equals `40`
   - Expected: simple_web_layout_debug_style_by_id(html, "e9", "margin_l") equals `10`
   - Expected: simple_web_layout_debug_style_by_id(html, "e9", "pad_l") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback path: the same full stage-2 property set plus one unhandled property gives the same result")
val html = "<html><head><style>#e9{justify-content:center;align-items:center;gap:8px;text-align:left;cursor:pointer;outline:2px solid #000;overflow:hidden;box-shadow:0 2px 4px #000;padding:5px;margin:10px;width:90px;height:40px;border-left:2px solid #000;}</style></head><body><div id=\"e9\">x</div></body></html>"
expect(simple_web_layout_debug_style_by_id(html, "e9", "width")).to_equal("90")
expect(simple_web_layout_debug_style_by_id(html, "e9", "height")).to_equal("40")
expect(simple_web_layout_debug_style_by_id(html, "e9", "margin_l")).to_equal("10")
expect(simple_web_layout_debug_style_by_id(html, "e9", "pad_l")).to_equal("5")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `843d79c32d6a9403dc0c37626067fff320742ce421ff2e864fee777b8e8ffcf4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `843d79c32d6a9403dc0c37626067fff320742ce421ff2e864fee777b8e8ffcf4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `843d79c32d6a9403dc0c37626067fff320742ce421ff2e864fee777b8e8ffcf4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'last-wins for the same property across two rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shorthand after longhand wins (background resets background-color)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'longhand after shorthand wins (background-color overrides background)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
