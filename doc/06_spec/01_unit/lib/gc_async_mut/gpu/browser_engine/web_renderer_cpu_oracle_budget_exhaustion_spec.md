# CPU Software Oracle — Budget Exhaustion Must Not Read As Success

> The pure-Simple CPU software renderer allocates its framebuffer at `width * height` **before** paint, so a render that trips its wall-clock budget returns a correctly-sized buffer holding only whatever finished before the deadline — commonly the canvas background and nothing else. Byte-shaped exactly like a successful render of a blank page, it used to be indistinguishable from one: a comparison against this oracle could pass by both sides being empty, or fail spuriously, depending only on host load.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU Software Oracle — Budget Exhaustion Must Not Read As Success

The pure-Simple CPU software renderer allocates its framebuffer at `width * height` **before** paint, so a render that trips its wall-clock budget returns a correctly-sized buffer holding only whatever finished before the deadline — commonly the canvas background and nothing else. Byte-shaped exactly like a successful render of a blank page, it used to be indistinguishable from one: a comparison against this oracle could pass by both sides being empty, or fail spuriously, depending only on host load.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The pure-Simple CPU software renderer allocates its framebuffer at
`width * height` **before** paint, so a render that trips its wall-clock budget
returns a correctly-sized buffer holding only whatever finished before the
deadline — commonly the canvas background and nothing else. Byte-shaped exactly
like a successful render of a blank page, it used to be indistinguishable from
one: a comparison against this oracle could pass by both sides being empty, or
fail spuriously, depending only on host load.

Reproduced deterministically by shrinking the budget rather than by loading the
host: the same page at a 600000 ms budget paints 596 ink pixels, and at a 1 ms
budget paints 0, with both returns being `[u32]` of length 6144.

This spec pins the honest signal:

- the verdict travels **on the result** (`render_degraded`, `degrade_reason`),
  not only in a module global that the next render clears;
- `degrade_reason` names a concrete exhaustion site from the enumerated
  `WEB_BUDGET_SITE_*` family, so a blank page can be attributed to a phase;
- `simple_web_layout_software_pixels_presentable` refuses to present it, and
  the decision string names the decline with a reason — the same shape as the
  GPU lane's `reason=readback-not-device-proven`;
- the honest direction holds too: a completed render must never report
  exhaustion.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### CPU software oracle budget exhaustion

#### returns a blank but correctly sized framebuffer when the budget is exhausted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a blank but correctly sized framebuffer when the budget is exhausted
- Render a text page under a generous 600s budget and count ink pixels
   - Expected: complete.pixels.len() equals `W * H`
   - Expected: _ink(complete.pixels) > 0 is true
- Render the identical page under a 1ms budget: same size, but no ink at all
   - Expected: starved.pixels.len() equals `W * H`
   - Expected: _ink(starved.pixels) equals `0`
- Confirm the two returns are pixel-buffer-indistinguishable in shape — the reason a status is required
   - Expected: starved.pixels.len() equals `complete.pixels.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a blank but correctly sized framebuffer when the budget is exhausted")
step("Render a text page under a generous 600s budget and count ink pixels")
val complete = simple_web_layout_render_html_software_result(INK_HTML, W, H, 600000)
expect(complete.pixels.len()).to_equal(W * H)
expect(_ink(complete.pixels) > 0).to_equal(true)
step("Render the identical page under a 1ms budget: same size, but no ink at all")
val starved = simple_web_layout_render_html_software_result(INK_HTML, W, H, 1)
expect(starved.pixels.len()).to_equal(W * H)
expect(_ink(starved.pixels)).to_equal(0)
step("Confirm the two returns are pixel-buffer-indistinguishable in shape — the reason a status is required")
expect(starved.pixels.len()).to_equal(complete.pixels.len())
```

</details>

#### carries the exhaustion verdict on the result instead of only in a module global

- carries the exhaustion verdict on the result instead of only in a module global
- Render starved, then render complete, and only THEN read both verdicts
- The global now reports the completed render, having forgotten the starved one
   - Expected: simple_web_layout_last_render_degraded() is false
- The starved result still reports its own exhaustion
   - Expected: starved.render_degraded is true
   - Expected: complete.render_degraded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries the exhaustion verdict on the result instead of only in a module global")
step("Render starved, then render complete, and only THEN read both verdicts")
# This is the ordering that makes a module global useless: an oracle-vs-lane
# comparison renders both sides before comparing. The global describes the
# LAST render; the result fields describe their own render.
val starved = simple_web_layout_render_html_software_result(INK_HTML, W, H, 1)
val complete = simple_web_layout_render_html_software_result(INK_HTML, W, H, 600000)
step("The global now reports the completed render, having forgotten the starved one")
expect(simple_web_layout_last_render_degraded()).to_equal(false)
step("The starved result still reports its own exhaustion")
expect(starved.render_degraded).to_equal(true)
expect(complete.render_degraded).to_equal(false)
```

</details>

#### names a concrete exhaustion site rather than degrading anonymously

- names a concrete exhaustion site rather than degrading anonymously
- Render under a 1ms budget and read the reason recorded on the result
   - Expected: starved.render_degraded is true
- The reason is non-empty and is one of the enumerated WEB_BUDGET_SITE_* names
   - Expected: starved.degrade_reason == "" is false
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names a concrete exhaustion site rather than degrading anonymously")
step("Render under a 1ms budget and read the reason recorded on the result")
val starved = simple_web_layout_render_html_software_result(INK_HTML, W, H, 1)
expect(starved.render_degraded).to_equal(true)
step("The reason is non-empty and is one of the enumerated WEB_BUDGET_SITE_* names")
expect(starved.degrade_reason == "").to_equal(false)
val known = (
    starved.degrade_reason == "style-cascade" or
    starved.degrade_reason == "style-selector-groups" or
    starved.degrade_reason == "style-candidate-decls" or
    starved.degrade_reason == "style-important-decls" or
    starved.degrade_reason == "layout-subtree" or
    starved.degrade_reason == "paint-backgrounds" or
    starved.degrade_reason == "paint-relative-roots" or
    starved.degrade_reason == "paint-absolute-low-z" or
    starved.degrade_reason == "paint-scrollbars" or
    starved.degrade_reason == "paint-text"
)
expect(known).to_equal(true)
```

</details>

#### refuses to present an exhausted render and names the decline with a reason

- refuses to present an exhausted render and names the decline with a reason
- An exhausted render is not presentable
   - Expected: simple_web_layout_software_pixels_presentable(starved) is false
- Its decision string declares the decline and carries the exhaustion site


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses to present an exhausted render and names the decline with a reason")
step("An exhausted render is not presentable")
val starved = simple_web_layout_render_html_software_result(INK_HTML, W, H, 1)
expect(simple_web_layout_software_pixels_presentable(starved)).to_equal(false)
step("Its decision string declares the decline and carries the exhaustion site")
val declined = simple_web_layout_software_present_decision(starved)
expect(declined).to_start_with("software-oracle:declined:")
expect(declined).to_contain("reason=budget-exhausted:")
expect(declined).to_contain(starved.degrade_reason)
```

</details>

#### presents a completed render and reports no exhaustion (the honest direction)

- presents a completed render and reports no exhaustion (the honest direction)
- A render with an adequate budget is presentable
   - Expected: complete.render_degraded is false
   - Expected: complete.degrade_reason equals ``
   - Expected: simple_web_layout_software_pixels_presentable(complete) is true
- Its decision string reports a full presented frame, never a decline
   - Expected: decision equals `software-oracle:presented:full-frame:reason=budget-complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("presents a completed render and reports no exhaustion (the honest direction)")
step("A render with an adequate budget is presentable")
val complete = simple_web_layout_render_html_software_result(INK_HTML, W, H, 600000)
expect(complete.render_degraded).to_equal(false)
expect(complete.degrade_reason).to_equal("")
expect(simple_web_layout_software_pixels_presentable(complete)).to_equal(true)
step("Its decision string reports a full presented frame, never a decline")
val decision = simple_web_layout_software_present_decision(complete)
expect(decision).to_equal("software-oracle:presented:full-frame:reason=budget-complete")
```

</details>

#### exposes the same verdict through the single-call probe entry

- exposes the same verdict through the single-call probe entry
- The probe entry declines under a starved budget
- and presents under a generous one
   - Expected: simple_web_layout_render_html_software_decision(INK_HTML, W, H, 600000) equals `software-oracle:presented:full-frame:reason=budget-complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes the same verdict through the single-call probe entry")
step("The probe entry declines under a starved budget")
expect(simple_web_layout_render_html_software_decision(INK_HTML, W, H, 1)).to_start_with("software-oracle:declined:")
step("and presents under a generous one")
expect(simple_web_layout_render_html_software_decision(INK_HTML, W, H, 600000)).to_equal("software-oracle:presented:full-frame:reason=budget-complete")
```

</details>

#### keeps the plain pixel entry working unchanged for existing callers

- keeps the plain pixel entry working unchanged for existing callers
- The [u32] entry still returns a full-size buffer with real ink under a normal budget
   - Expected: pixels.len() equals `W * H`
   - Expected: _ink(pixels) > 0 is true
   - Expected: simple_web_layout_last_render_degrade_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the plain pixel entry working unchanged for existing callers")
step("The [u32] entry still returns a full-size buffer with real ink under a normal budget")
val pixels = simple_web_layout_render_html_software_pixels(INK_HTML, W, H, 600000)
expect(pixels.len()).to_equal(W * H)
expect(_ink(pixels) > 0).to_equal(true)
expect(simple_web_layout_last_render_degrade_reason()).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `08e5ef9154fb8f9800d86c60c240ea93e55a862803986ae4d381721c6b5bf9dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08e5ef9154fb8f9800d86c60c240ea93e55a862803986ae4d381721c6b5bf9dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08e5ef9154fb8f9800d86c60c240ea93e55a862803986ae4d381721c6b5bf9dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a blank but correctly sized framebuffer when the budget is exhausted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the exhaustion verdict on the result instead of only in a module global' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_oracle_budget_exhaustion_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names a concrete exhaustion site rather than degrading anonymously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
