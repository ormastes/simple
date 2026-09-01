# Simple Web Negative Margin Collapsing Specification

> Proves that the pure-Simple HTML/CSS block layout collapses adjacent vertical margins per CSS 2.2 §8.3.1 (`max(positive margins) + min(negative margins)`) rather than a plain `max()`, which is only correct when every margin involved is non-negative.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Negative Margin Collapsing Specification

Proves that the pure-Simple HTML/CSS block layout collapses adjacent vertical margins per CSS 2.2 §8.3.1 (`max(positive margins) + min(negative margins)`) rather than a plain `max()`, which is only correct when every margin involved is non-negative.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that the pure-Simple HTML/CSS block layout collapses adjacent
vertical margins per CSS 2.2 §8.3.1 (`max(positive margins) + min(negative
margins)`) rather than a plain `max()`, which is only correct when every
margin involved is non-negative.

Two compounding defects were found and fixed together:

1. `margin_token_vh_px()` in `simple_web_html_layout_renderer_foundation.spl`
   fed a literal margin token straight into `parse_int()`, which only
   accumulates digits and silently drops a leading `-`, so `-10px` parsed as
   `10`. `resolve_vertical_margin_px()` in
   `simple_web_html_layout_renderer_layout.spl` then additionally clamped any
   remaining negative value (the -999..-1 range) to `0` — that range was
   meant to be dead space, reachable only because `parse_int()` could never
   itself return a negative value, so nothing distinguished "unset" from "a
   genuine negative px margin".
2. The block-flow collapse itself, at three sites in
   `simple_web_html_layout_renderer_layout.spl`, inlined a plain `max()`
   (`if a > b: a else: b`) instead of the correct CSS formula. A pure,
   already-written (but until now unused) helper for that formula already
   existed: `collapse_margins_signed()` in `layout_m14_types.spl`.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### Simple Web negative margin collapsing (CSS 2.2 8.3.1)

#### combines a negative margin-bottom with a positive margin-top (max(0,20) + min(-10,0) = 10)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- combines a negative margin-bottom with a positive margin-top (max(0,20) + min(-10,0) = 10)
- Render a -10px margin-bottom block followed by a 20px margin-top block
   - Expected: _layout_field(html, "a", "y") equals `0`
   - Expected: _layout_field(html, "a", "h") equals `20`
   - Expected: _layout_field(html, "b", "y") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("combines a negative margin-bottom with a positive margin-top (max(0,20) + min(-10,0) = 10)")
step("Render a -10px margin-bottom block followed by a 20px margin-top block")
val html = _positive_and_negative_html()
expect(_layout_field(html, "a", "y")).to_equal(0)
expect(_layout_field(html, "a", "h")).to_equal(20)
# Plain max(-10, 20) would wrongly give 20 (b.y = 40). Correct CSS
# collapse is max(0,20) + min(-10,0) = 10, so b.y = 20 + 10 = 30.
expect(_layout_field(html, "b", "y")).to_equal(30)
```

</details>

#### takes the more-negative margin when both adjoining margins are negative (min(-10,-20) = -20)

- takes the more-negative margin when both adjoining margins are negative (min(-10,-20) = -20)
- Render a -10px margin-bottom block followed by a -20px margin-top block
   - Expected: _layout_field(html, "c", "y") equals `0`
   - Expected: _layout_field(html, "c", "h") equals `20`
   - Expected: _layout_field(html, "d", "y") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("takes the more-negative margin when both adjoining margins are negative (min(-10,-20) = -20)")
step("Render a -10px margin-bottom block followed by a -20px margin-top block")
val html = _both_negative_html()
expect(_layout_field(html, "c", "y")).to_equal(0)
expect(_layout_field(html, "c", "h")).to_equal(20)
# Plain max(-10, -20) would wrongly give -10 (d.y = 10). Correct CSS
# collapse is max(0,0) + min(-10,-20) = -20, so d.y = 20 - 20 = 0.
expect(_layout_field(html, "d", "y")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `5ee2279afce4185a472ad19a54b400283dfe6911e324e9e48658a4364413b584`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ee2279afce4185a472ad19a54b400283dfe6911e324e9e48658a4364413b584`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ee2279afce4185a472ad19a54b400283dfe6911e324e9e48658a4364413b584`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'combines a negative margin-bottom with a positive margin-top (max(0,20) + min(-10,0) = 10)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the more-negative margin when both adjoining margins are negative (min(-10,-20) = -20)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
