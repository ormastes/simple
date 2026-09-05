# Browser Renderer Gradient Stops Wiring Specification

> Tests covering GAP-2 apply_decls populates the N-stop gradient Style fields, GAP-2 HTML to pixels through draw_ir_adv stop-list painting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Gradient Stops Wiring Specification

## Scenarios

### GAP-2 apply_decls populates the N-stop gradient Style fields

#### parses a 3-stop angled linear-gradient into stop colors/positions/angle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a 3-stop angled linear-gradient into stop colors/positions/angle
   - Expected: st1.background_gradient_stop_colors.len() equals `3`
   - Expected: st1.background_gradient_stop_positions.len() equals `3`
   - Expected: st1.background_gradient_angle_deg equals `45`
   - Expected: st1.background_gradient_is_radial is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a 3-stop angled linear-gradient into stop colors/positions/angle")
val st0 = renderer_default_style()
val st1 = apply_decls(st0, "background-image: linear-gradient(45deg, #ff0000, #ffff00, #0000ff);", 16)
expect(st1.background_gradient_stop_colors.len()).to_equal(3)
expect(st1.background_gradient_stop_positions.len()).to_equal(3)
expect(st1.background_gradient_angle_deg).to_equal(45)
expect(st1.background_gradient_is_radial).to_equal(false)
```

</details>

#### parses a radial-gradient into stop fields with the radial flag

- parses a radial-gradient into stop fields with the radial flag
   - Expected: st2.background_gradient_stop_colors.len() equals `3`
   - Expected: st2.background_gradient_is_radial is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a radial-gradient into stop fields with the radial flag")
val st0 = renderer_default_style()
val st2 = apply_decls(st0, "background-image: radial-gradient(#ff0000, #ffff00, #0000ff);", 16)
expect(st2.background_gradient_stop_colors.len()).to_equal(3)
expect(st2.background_gradient_is_radial).to_equal(true)
```

</details>

#### resets the stop fields on a later background-image none

- resets the stop fields on a later background-image none
   - Expected: st2.background_gradient_stop_colors.len() equals `0`
   - Expected: st2.background_gradient_is_radial is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resets the stop fields on a later background-image none")
val st0 = renderer_default_style()
val st1 = apply_decls(st0, "background-image: linear-gradient(45deg, #ff0000, #ffff00, #0000ff);", 16)
val st2 = apply_decls(st1, "background-image: none;", 16)
expect(st2.background_gradient_stop_colors.len()).to_equal(0)
expect(st2.background_gradient_is_radial).to_equal(false)
```

</details>

### GAP-2 HTML to pixels through draw_ir_adv stop-list painting

#### renders a 3-stop 45deg linear gradient with many distinct shades

- renders a 3-stop 45deg linear gradient with many distinct shades
   - Expected: distinct_non_white(px) >= 10 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a 3-stop 45deg linear gradient with many distinct shades")
val html = "<html><body><span style='display:block; width: 20px; height: 20px; background-image: linear-gradient(45deg, #ff0000, #ffff00, #0000ff)'></span></body></html>"
val px = simple_web_layout_render_html_pixels_engine2d(html, 30, 30, "software")
expect(distinct_non_white(px) >= 10).to_equal(true)
```

</details>

#### renders a radial gradient with multiple distinct rings

- renders a radial gradient with multiple distinct rings
   - Expected: distinct_non_white(px) >= 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a radial gradient with multiple distinct rings")
val html = "<html><body><span style='display:block; width: 20px; height: 20px; background-image: radial-gradient(#ff0000, #ffff00, #0000ff)'></span></body></html>"
val px = simple_web_layout_render_html_pixels_engine2d(html, 30, 30, "software")
expect(distinct_non_white(px) >= 5).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GAP-2 apply_decls populates the N-stop gradient Style fields, GAP-2 HTML to pixels through draw_ir_adv stop-list painting.
- GAP-2 apply_decls populates the N-stop gradient Style fields
- GAP-2 HTML to pixels through draw_ir_adv stop-list painting

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

- Canonical SPipe generation for source `64b08e191d4031a4adaf543bf4a383cbed733e6fa282cbe001eefc659f0024dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64b08e191d4031a4adaf543bf4a383cbed733e6fa282cbe001eefc659f0024dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64b08e191d4031a4adaf543bf4a383cbed733e6fa282cbe001eefc659f0024dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a 3-stop angled linear-gradient into stop colors/positions/angle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a radial-gradient into stop fields with the radial flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_gradient_stops_wiring_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets the stop fields on a later background-image none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
