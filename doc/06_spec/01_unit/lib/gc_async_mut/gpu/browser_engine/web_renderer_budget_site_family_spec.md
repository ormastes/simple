# Every Budget Exit Must Name A Site That Actually Exists

> `40c540fa850` replaced the anonymous `_web_budget_expired()` with `_web_budget_expired_at(site)` so that no budget-exhaustion exit could be nameless, and enumerated the family as ten `WEB_BUDGET_SITE_*` constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Every Budget Exit Must Name A Site That Actually Exists

`40c540fa850` replaced the anonymous `_web_budget_expired()` with `_web_budget_expired_at(site)` so that no budget-exhaustion exit could be nameless, and enumerated the family as ten `WEB_BUDGET_SITE_*` constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`40c540fa850` replaced the anonymous `_web_budget_expired()` with
`_web_budget_expired_at(site)` so that no budget-exhaustion exit could be
nameless, and enumerated the family as ten `WEB_BUDGET_SITE_*` constants.

The rename reached the layout and paint guards but **missed the style phase**.
Four call sites in `simple_web_html_layout_renderer_core.spl` (the style
cascade's outer node loop, the selector-specificity-group loop, the candidate
declaration loop and the important-declaration loop) kept calling the
zero-argument `_web_budget_expired()`, which no longer exists anywhere. The four
`WEB_BUDGET_SITE_STYLE_*` constants were consequently declared and never used.

Two things followed, and both are the "silent" failure this family exists to
prevent:

1. the unresolved symbol made the JIT drop the **entire style module to the
   interpreter** (`unresolved external symbol '_web_budget_expired': whole
   module dropped to the interpreter`), a 100-1000x slowdown on the phase that
   the budget is meant to bound -- so exhaustion became far more likely;
2. when a style guard was actually reached, the render died with
   `error[E1002]: function '_web_budget_expired' not found` instead of degrading.

Existing specs did not catch it because their pages are small enough that the
render finishes before the interpreter penalty matters, and because a spec that
only checks "the reason is one of the family" is satisfied by any paint site.

This spec pins the style phase specifically: a style-heavy page on a starved
budget must degrade **at a style site**, which is only possible if those four
guards call a function that exists.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### budget site family

#### degrades at a STYLE site on a style-heavy page, proving the style guards resolve

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- degrades at a STYLE site on a style-heavy page, proving the style guards resolve
- Render a style-heavy page on a 1ms budget
   - Expected: starved.render_degraded is true
- The named site is a style site, not a paint site
   - Expected: starved.degrade_reason equals `style-cascade`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("degrades at a STYLE site on a style-heavy page, proving the style guards resolve")
step("Render a style-heavy page on a 1ms budget")
# Before the fix this did not merely report the wrong site: it raised
# error[E1002] `_web_budget_expired` not found and the render died.
val starved = simple_web_layout_render_html_software_result(_style_heavy_page(120), W, H, 1)
expect(starved.render_degraded).to_equal(true)
step("The named site is a style site, not a paint site")
expect(starved.degrade_reason).to_equal("style-cascade")
```

</details>

#### names a site from the enumerated family whatever the page

- names a site from the enumerated family whatever the page
- A starved style-heavy render names a known site
   - Expected: heavy.degrade_reason == "" is false
   - Expected: _is_known_site(heavy.degrade_reason) is true
- A starved small render also names a known site
   - Expected: small.render_degraded is true
   - Expected: _is_known_site(small.degrade_reason) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names a site from the enumerated family whatever the page")
step("A starved style-heavy render names a known site")
val heavy = simple_web_layout_render_html_software_result(_style_heavy_page(120), W, H, 1)
expect(heavy.degrade_reason == "").to_equal(false)
expect(_is_known_site(heavy.degrade_reason)).to_equal(true)
step("A starved small render also names a known site")
val small = simple_web_layout_render_html_software_result(SMALL_PAGE, W, H, 1)
expect(small.render_degraded).to_equal(true)
expect(_is_known_site(small.degrade_reason)).to_equal(true)
```

</details>

#### refuses to present the exhausted style render and names the decline

- refuses to present the exhausted style render and names the decline
- An exhausted render is not presentable
   - Expected: simple_web_layout_software_pixels_presentable(starved) is false
- The decision string carries the style site as the concrete reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses to present the exhausted style render and names the decline")
step("An exhausted render is not presentable")
val starved = simple_web_layout_render_html_software_result(_style_heavy_page(120), W, H, 1)
expect(simple_web_layout_software_pixels_presentable(starved)).to_equal(false)
step("The decision string carries the style site as the concrete reason")
val declined = simple_web_layout_software_present_decision(starved)
expect(declined).to_start_with("software-oracle:declined:")
expect(declined).to_contain("reason=budget-exhausted:")
expect(declined).to_contain(starved.degrade_reason)
```

</details>

#### reports no exhaustion when the budget is adequate (the honest direction)

- reports no exhaustion when the budget is adequate (the honest direction)
- A small page under a generous budget completes and names nothing
   - Expected: complete.render_degraded is false
   - Expected: complete.degrade_reason equals ``
   - Expected: simple_web_layout_software_pixels_presentable(complete) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports no exhaustion when the budget is adequate (the honest direction)")
step("A small page under a generous budget completes and names nothing")
val complete = simple_web_layout_render_html_software_result(SMALL_PAGE, W, H, 600000)
expect(complete.render_degraded).to_equal(false)
expect(complete.degrade_reason).to_equal("")
expect(simple_web_layout_software_pixels_presentable(complete)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ebe75864921a261cfff036b97520a7d223a3ca4e3826a6e9d2f99d628c140f55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebe75864921a261cfff036b97520a7d223a3ca4e3826a6e9d2f99d628c140f55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebe75864921a261cfff036b97520a7d223a3ca4e3826a6e9d2f99d628c140f55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'degrades at a STYLE site on a style-heavy page, proving the style guards resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names a site from the enumerated family whatever the page' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_budget_site_family_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to present the exhausted style render and names the decline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
