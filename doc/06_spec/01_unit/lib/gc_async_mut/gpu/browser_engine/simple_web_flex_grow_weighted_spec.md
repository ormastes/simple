# Simple Web Flex-Grow Weighted Distribution Specification

> Proves that the pure-Simple HTML/CSS layout renderer distributes a flex row's leftover main-axis space in proportion to each child's `flex-grow` weight (not in equal shares), and that `flex-wrap: wrap-reverse` places the first flex line at the bottom with wrapped lines stacking upward.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Flex-Grow Weighted Distribution Specification

Proves that the pure-Simple HTML/CSS layout renderer distributes a flex row's leftover main-axis space in proportion to each child's `flex-grow` weight (not in equal shares), and that `flex-wrap: wrap-reverse` places the first flex line at the bottom with wrapped lines stacking upward.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that the pure-Simple HTML/CSS layout renderer distributes a flex row's
leftover main-axis space in proportion to each child's `flex-grow` weight
(not in equal shares), and that `flex-wrap: wrap-reverse` places the first
flex line at the bottom with wrapped lines stacking upward.

These are regression guards for the historically deferred defect where the
renderer split leftover space equally among auto children instead of honoring
`flex-grow` ratios.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### Simple Web flex-grow weighted distribution

#### distributes leftover space by flex-grow ratio 1:2:1 in a 400px row

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- distributes leftover space by flex-grow ratio 1:2:1 in a 400px row
- Render three flex-grow children (1/2/1) with no explicit width in a 400px container
   - Expected: _layout_field(html, "a", "w") equals `100`
   - Expected: _layout_field(html, "b", "w") equals `200`
   - Expected: _layout_field(html, "c", "w") equals `100`
- Confirm the widths are weighted, not equal thirds (would be ~133 each)
   - Expected: _layout_field(html, "c", "x") equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distributes leftover space by flex-grow ratio 1:2:1 in a 400px row")
step("Render three flex-grow children (1/2/1) with no explicit width in a 400px container")
val html = _grow_1_2_1_html()
# Leftover main space = 400 (no fixed children). 1:2:1 of 400 => 100/200/100.
expect(_layout_field(html, "a", "w")).to_equal(100)
expect(_layout_field(html, "b", "w")).to_equal(200)
expect(_layout_field(html, "c", "w")).to_equal(100)
step("Confirm the widths are weighted, not equal thirds (would be ~133 each)")
expect(_layout_field(html, "b", "w")).to_be_greater_than(_layout_field(html, "a", "w"))
expect(_layout_field(html, "c", "x")).to_equal(300)
```

</details>

#### weights leftover against a fixed sibling (fixed 40px + flex 1/2 in 240px)

- weights leftover against a fixed sibling (fixed 40px + flex 1/2 in 240px)
- Render a 40px fixed child plus flex:1 and flex:2 children in a 240px container
   - Expected: _layout_field(html, "f", "w") equals `40`
   - Expected: _layout_field(html, "a", "w") equals `67`
   - Expected: _layout_field(html, "b", "w") equals `133`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("weights leftover against a fixed sibling (fixed 40px + flex 1/2 in 240px)")
step("Render a 40px fixed child plus flex:1 and flex:2 children in a 240px container")
val html = _grow_fixed_1_2_html()
# Leftover after the 40px fixed child = 200; 1:2 => 67/133 (integer rounding).
expect(_layout_field(html, "f", "w")).to_equal(40)
expect(_layout_field(html, "a", "w")).to_equal(67)
expect(_layout_field(html, "b", "w")).to_equal(133)
```

</details>

#### places wrap-reverse first line at the bottom and wrapped line on top

- places wrap-reverse first line at the bottom and wrapped line on top
- Render three 60px children in a 140px wrap-reverse row (16px body-ish margin)
   - Expected: _layout_field(html, "a", "y") equals `40`
   - Expected: _layout_field(html, "b", "y") equals `40`
   - Expected: _layout_field(html, "c", "y") equals `16`
   - Expected: _layout_field(html, "a", "x") equals `16`
   - Expected: _layout_field(html, "c", "x") equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places wrap-reverse first line at the bottom and wrapped line on top")
step("Render three 60px children in a 140px wrap-reverse row (16px body-ish margin)")
val html = _wrap_reverse_html()
# a+b fill the first line (60+60=120 <= 140); c wraps. wrap-reverse puts the
# first line at the bottom (y=40) and the wrapped line on top (y=16).
expect(_layout_field(html, "a", "y")).to_equal(40)
expect(_layout_field(html, "b", "y")).to_equal(40)
expect(_layout_field(html, "c", "y")).to_equal(16)
expect(_layout_field(html, "a", "x")).to_equal(16)
expect(_layout_field(html, "c", "x")).to_equal(16)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `0f3e7cd3067c7148d94957ddfe5cf88989ec9edc0e614bee9e495b6c1465be9a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f3e7cd3067c7148d94957ddfe5cf88989ec9edc0e614bee9e495b6c1465be9a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f3e7cd3067c7148d94957ddfe5cf88989ec9edc0e614bee9e495b6c1465be9a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distributes leftover space by flex-grow ratio 1:2:1 in a 400px row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'weights leftover against a fixed sibling (fixed 40px + flex 1/2 in 240px)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places wrap-reverse first line at the bottom and wrapped line on top' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
