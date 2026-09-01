# Every Paint Pass, Including Positive-Z Absolute, Must Name Its Budget Exit

> The CPU software paint path runs six passes. Five of them (backgrounds, relative roots, absolute low-z, scrollbars, text) begin with

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Every Paint Pass, Including Positive-Z Absolute, Must Name Its Budget Exit

The CPU software paint path runs six passes. Five of them (backgrounds, relative roots, absolute low-z, scrollbars, text) begin with

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The CPU software paint path runs six passes. Five of them
(backgrounds, relative roots, absolute low-z, scrollbars, text) begin with

    if _web_budget_expired_at(WEB_BUDGET_SITE_...): break

Pass 4 -- the positive-z absolute boxes, walked in z-sorted order -- had **no
guard at all**. It was the only member of the family that could not name an exit.

It is bounded by `positive_z_count` rather than `node_count`, so it was never
runaway, and that is exactly why the gap survived: "bounded" was read as "safe".
Bounded is not free. Each iteration walks `content_paint_hidden_by_ancestor` and
can rasterise a box shadow or gradient over the whole box area, and passes 5
(scrollbars) and 6 (text) run *after* it. A page whose positive-z absolute boxes
are large therefore burned the remainder of the paint slice in pass 4 and
starved the text pass -- yielding a page-shaped frame with no text on it while
attributing the degrade to `paint-scrollbars` or `paint-text`, which is the
wrong phase. Asymmetry is how the next silent truncation hides.

Pass 4 now names `paint-absolute-high-z`, the eleventh member of the family.

## Why these arms are structural rather than timed

The behavioural arm was measured and does work, but only outside a spec.
Driving the renderer from `simple run` (JIT), a style-light / paint-heavy
fixture of 24 large positive-z absolute boxes reports `paint-absolute-high-z`
at **every budget from 240ms to 3000ms inclusive (10/10 sampled points)** --
a stable plateau over a 12x range.

Specs, however, execute interpreted, where the same fixture is ~100x slower:
the transition moves above **24s** per render and the plateau becomes both
expensive and load-sensitive (this host routinely runs 20+ concurrent `simple`
processes). Gating on a tuned wall-clock budget there would produce a flaky
gate, and a flaky gate is worse than none.

So the timed arm is recorded as measured-but-not-gated, and the gate is the
broader structural invariant instead: **every paint pass names a site, and the
anonymous `_web_budget_expired()` exists nowhere.** That invariant is exactly
what both defects violated -- pass 4 naming nothing, and the four style guards
calling a name that no longer existed -- and unlike the timed arm it bites
deterministically and instantly.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### paint pass budget exit naming

#### reads the renderer sources it is about to assert on (guards against a vacuous pass)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the renderer sources it is about to assert on (guards against a vacuous pass)
- Each source is non-empty, so a failed read cannot make the arms below trivially true
   - Expected: _src(PAINT_SRC).len() > 10000 is true
   - Expected: _src(FOUNDATION_SRC).len() > 10000 is true
   - Expected: _src(CORE_SRC).len() > 10000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the renderer sources it is about to assert on (guards against a vacuous pass)")
step("Each source is non-empty, so a failed read cannot make the arms below trivially true")
expect(_src(PAINT_SRC).len() > 10000).to_equal(true)
expect(_src(FOUNDATION_SRC).len() > 10000).to_equal(true)
expect(_src(CORE_SRC).len() > 10000).to_equal(true)
```

</details>

#### declares the positive-z paint site in the enumerated family

- declares the positive-z paint site in the enumerated family
- The eleventh site constant exists alongside the original ten


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declares the positive-z paint site in the enumerated family")
step("The eleventh site constant exists alongside the original ten")
expect(_src(FOUNDATION_SRC)).to_contain("WEB_BUDGET_SITE_PAINT_ABSOLUTE_HIGH_Z: text = \"paint-absolute-high-z\"")
```

</details>

#### guards the positive-z absolute paint pass with that site

- guards the positive-z absolute paint pass with that site
- Pass 4 tests the deadline and names itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards the positive-z absolute paint pass with that site")
step("Pass 4 tests the deadline and names itself")
expect(_src(PAINT_SRC)).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_ABSOLUTE_HIGH_Z)")
```

</details>

#### guards all six paint passes, leaving none anonymous or unguarded

- guards all six paint passes, leaving none anonymous or unguarded
- Passes 1, 2 and 3
- Pass 4 -- the one that previously had no guard
- Passes 5 and 6, which run after pass 4 and were the ones it starved


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards all six paint passes, leaving none anonymous or unguarded")
val paint = _src(PAINT_SRC)
step("Passes 1, 2 and 3")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_BACKGROUNDS)")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_RELATIVE_ROOTS)")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_ABSOLUTE_LOW_Z)")
step("Pass 4 -- the one that previously had no guard")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_ABSOLUTE_HIGH_Z)")
step("Passes 5 and 6, which run after pass 4 and were the ones it starved")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_SCROLLBARS)")
expect(paint).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_PAINT_TEXT)")
```

</details>

#### wires every style guard to a named site instead of a function that does not exist

- wires every style guard to a named site instead of a function that does not exist
- All four style sites are called, not merely declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wires every style guard to a named site instead of a function that does not exist")
val core = _src(CORE_SRC)
step("All four style sites are called, not merely declared")
expect(core).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_STYLE_CASCADE)")
expect(core).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_STYLE_SELECTOR_GROUPS)")
expect(core).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_STYLE_CANDIDATE_DECLS)")
expect(core).to_contain("_web_budget_expired_at(WEB_BUDGET_SITE_STYLE_IMPORTANT_DECLS)")
```

</details>

#### leaves no anonymous budget test anywhere in the renderer

- leaves no anonymous budget test anywhere in the renderer
- `_web_budget_expired()` takes no site and therefore cannot be attributed; it must not exist
   - Expected: _src(CORE_SRC) does not contain `_web_budget_expired():`
   - Expected: _src(PAINT_SRC) does not contain `_web_budget_expired():`
   - Expected: _src(LAYOUT_SRC) does not contain `_web_budget_expired():`
   - Expected: _src(FOUNDATION_SRC) does not contain `fn _web_budget_expired():`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves no anonymous budget test anywhere in the renderer")
step("`_web_budget_expired()` takes no site and therefore cannot be attributed; it must not exist")
# It also does not exist as a definition, so any surviving call both
# drops the module to the interpreter and dies with E1002 when reached.
expect(_src(CORE_SRC).contains("_web_budget_expired():")).to_equal(false)
expect(_src(PAINT_SRC).contains("_web_budget_expired():")).to_equal(false)
expect(_src(LAYOUT_SRC).contains("_web_budget_expired():")).to_equal(false)
expect(_src(FOUNDATION_SRC).contains("fn _web_budget_expired():")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `fbe792047e13683d1e3302e9f17961b92e854a269e5e1f8564927ddca89a40ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbe792047e13683d1e3302e9f17961b92e854a269e5e1f8564927ddca89a40ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbe792047e13683d1e3302e9f17961b92e854a269e5e1f8564927ddca89a40ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the renderer sources it is about to assert on (guards against a vacuous pass)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares the positive-z paint site in the enumerated family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_positive_z_paint_budget_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards the positive-z absolute paint pass with that site' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
