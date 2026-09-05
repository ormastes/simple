# Simple Web HTML Hidden Attribute Specification

> The canonical HTML semantic/style pipeline treats the boolean `hidden`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web HTML Hidden Attribute Specification

The canonical HTML semantic/style pipeline treats the boolean `hidden`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The canonical HTML semantic/style pipeline treats the boolean `hidden`
attribute as a lowest-priority presentational default. Author CSS may override
it. The distinct `hidden="until-found"` state remains unsupported.

## Scenarios

### Simple Web HTML hidden attribute

#### suppresses an exact hidden subtree in software and Draw IR

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- suppresses an exact hidden subtree in software and Draw IR
   - Expected: simple_web_layout_debug_style_by_id(html, "hidden", "display") equals `none`
   - Expected: _command_index(commands, "hidden") equals `-1`
   - Expected: _command_index(commands, "child") equals `-1`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("suppresses an exact hidden subtree in software and Draw IR")
val html = "<html><head><style>html,body{margin:0;background:#fff}.panel{width:8px;height:8px;background:#ef4444}</style></head><body><section id='hidden' hidden><div id='child' class='panel'></div></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 16, 16)
val commands = composition.batches[0].commands
val pixels = simple_web_layout_render_html_software_pixels(html, 16, 16)

expect(simple_web_layout_debug_style_by_id(html, "hidden", "display")).to_equal("none")
expect(_command_index(commands, "hidden")).to_equal(-1)
expect(_command_index(commands, "child")).to_equal(-1)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### does not confuse similarly named or quoted attributes with hidden

- does not confuse similarly named or quoted attributes with hidden
   - Expected: simple_web_layout_debug_style_by_id(html, "data", "display") equals `block`
   - Expected: simple_web_layout_debug_style_by_id(html, "suffix", "display") equals `block`
   - Expected: simple_web_layout_debug_style_by_id(html, "quoted", "display") equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not confuse similarly named or quoted attributes with hidden")
val html = "<html><body><section id='data' data-hidden></section><section id='suffix' hiddenx></section><section id='quoted' title=' hidden '></section></body></html>"

expect(simple_web_layout_debug_style_by_id(html, "data", "display")).to_equal("block")
expect(simple_web_layout_debug_style_by_id(html, "suffix", "display")).to_equal("block")
expect(simple_web_layout_debug_style_by_id(html, "quoted", "display")).to_equal("block")
```

</details>

#### keeps hidden until-found outside the supported plain-hidden subset

- keeps hidden until-found outside the supported plain-hidden subset
   - Expected: simple_web_layout_debug_style_by_id(html, "future", "display") equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps hidden until-found outside the supported plain-hidden subset")
val html = "<html><body><section Id='future' HiDdEn='until-found'></section></body></html>"

expect(simple_web_layout_debug_style_by_id(html, "future", "display")).to_equal("block")
```

</details>

#### matches mixed-case HTML attribute names without folding values

- matches mixed-case HTML attribute names without folding values
   - Expected: simple_web_layout_debug_style_by_id(html, "MiXeD", "display") equals `none`
   - Expected: simple_web_layout_debug_style_by_id(html, "class-sanity", "display") equals `inline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches mixed-case HTML attribute names without folding values")
val html = "<html><head><style>.probe{display:inline}</style></head><body><section ID='MiXeD' ClAsS='probe' HIDDEN></section><section iD='class-sanity' cLaSs='probe'></section></body></html>"

expect(simple_web_layout_debug_style_by_id(html, "MiXeD", "display")).to_equal("none")
expect(simple_web_layout_debug_style_by_id(html, "class-sanity", "display")).to_equal("inline")
```

</details>

#### lets author display override the hidden presentational default

- lets author display override the hidden presentational default
   - Expected: simple_web_layout_debug_style_by_id(html, "shown", "display") equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets author display override the hidden presentational default")
val html = "<html><head><style>html,body{margin:0;background:#fff}#shown{display:block;width:8px;height:8px;background:#22c55e}</style></head><body><section id='shown' hidden></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 16, 16)
val commands = composition.batches[0].commands
val pixels = simple_web_layout_render_html_software_pixels(html, 16, 16)

expect(simple_web_layout_debug_style_by_id(html, "shown", "display")).to_equal("block")
expect(_command_index(commands, "shown")).to_be_greater_than(-1)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9dc5fb09e23a23eb93b92afffdc14fee02c6553b375307d54197cb7410c9bff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9dc5fb09e23a23eb93b92afffdc14fee02c6553b375307d54197cb7410c9bff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9dc5fb09e23a23eb93b92afffdc14fee02c6553b375307d54197cb7410c9bff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suppresses an exact hidden subtree in software and Draw IR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not confuse similarly named or quoted attributes with hidden' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_hidden_attribute_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps hidden until-found outside the supported plain-hidden subset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
