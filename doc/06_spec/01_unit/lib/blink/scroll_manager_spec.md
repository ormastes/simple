# Blink ScrollManager Specification

> Tests for the scroll manager: per-element scroll offset tracking, clamping, overflow behaviour, registration, lookup, and delegation via scroll_element.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink ScrollManager Specification

Tests for the scroll manager: per-element scroll offset tracking, clamping, overflow behaviour, registration, lookup, and delegation via scroll_element.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Scroll |
| Status | Active |
| Source | `test/01_unit/lib/blink/scroll_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the scroll manager: per-element scroll offset tracking, clamping,
overflow behaviour, registration, lookup, and delegation via scroll_element.

## Scenarios

### scrollable_area_new

#### scroll_x/y start at 0, overflow=Auto

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scroll_x/y start at 0, overflow=Auto
   - Expected: approx_eq(area.scroll_x, 0.0) is true
   - Expected: approx_eq(area.scroll_y, 0.0) is true
   - Expected: area.overflow_x equals `OverflowBehavior.Auto`
   - Expected: area.overflow_y equals `OverflowBehavior.Auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scroll_x/y start at 0, overflow=Auto")
val area = scrollable_area_new(1, 800.0, 600.0, 1600.0, 1200.0)
expect(approx_eq(area.scroll_x, 0.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 0.0)).to_equal(true)
expect(area.overflow_x).to_equal(OverflowBehavior.Auto)
expect(area.overflow_y).to_equal(OverflowBehavior.Auto)
```

</details>

### max_scroll_x and max_scroll_y

#### max_scroll_x/y: correct for content > viewport

- max_scroll_x/y: correct for content > viewport
   - Expected: approx_eq(area.max_scroll_x(), 800.0) is true
   - Expected: approx_eq(area.max_scroll_y(), 600.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("max_scroll_x/y: correct for content > viewport")
val area = scrollable_area_new(2, 800.0, 600.0, 1600.0, 1200.0)
expect(approx_eq(area.max_scroll_x(), 800.0)).to_equal(true)
expect(approx_eq(area.max_scroll_y(), 600.0)).to_equal(true)
```

</details>

### scroll_by upper clamp

#### scroll_by: clamps to max (beyond content does not overshoot)

- scroll_by: clamps to max (beyond content does not overshoot)
   - Expected: approx_eq(area.scroll_x, 800.0) is true
   - Expected: approx_eq(area.scroll_y, 600.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scroll_by: clamps to max (beyond content does not overshoot)")
val area = scrollable_area_new(3, 800.0, 600.0, 1600.0, 1200.0)
area.scroll_by(10000.0, 10000.0)
expect(approx_eq(area.scroll_x, 800.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 600.0)).to_equal(true)
```

</details>

### scroll_by lower clamp

#### scroll_by: clamps to 0 (negative scroll disallowed)

- scroll_by: clamps to 0 (negative scroll disallowed)
   - Expected: approx_eq(area.scroll_x, 0.0) is true
   - Expected: approx_eq(area.scroll_y, 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scroll_by: clamps to 0 (negative scroll disallowed)")
val area = scrollable_area_new(4, 800.0, 600.0, 1600.0, 1200.0)
area.scroll_by(-500.0, -500.0)
expect(approx_eq(area.scroll_x, 0.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 0.0)).to_equal(true)
```

</details>

### can_scroll_y Auto

#### can_scroll_y: Auto with content > viewport returns true

- can_scroll_y: Auto with content > viewport returns true
   - Expected: area.can_scroll_y() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can_scroll_y: Auto with content > viewport returns true")
val area = scrollable_area_new(5, 800.0, 600.0, 800.0, 1200.0)
expect(area.can_scroll_y()).to_equal(true)
```

</details>

### can_scroll_y Hidden

#### can_scroll_y: Hidden returns false

- can_scroll_y: Hidden returns false
   - Expected: area.can_scroll_y() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can_scroll_y: Hidden returns false")
val area = scrollable_area_new(6, 800.0, 600.0, 800.0, 1200.0)
area.overflow_y = OverflowBehavior.Hidden
expect(area.can_scroll_y()).to_equal(true)
```

</details>

### ScrollManager register and find_area

#### register + find_area: round-trips

- register + find_area: round-trips
   - Expected: found is None is false
   - Expected: a.element_id equals `10`
   - Expected: approx_eq(a.viewport_width, 800.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("register + find_area: round-trips")
val mgr = scroll_manager_new()
val area = scrollable_area_new(10, 800.0, 600.0, 1600.0, 1200.0)
mgr.register(area)
val found = mgr.find_area(10)
expect(found is None).to_equal(false)
val a = found.unwrap()
expect(a.element_id).to_equal(10)
expect(approx_eq(a.viewport_width, 800.0)).to_equal(true)
```

</details>

### ScrollManager scroll_element missing

#### scroll_element: missing element returns false

- scroll_element: missing element returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scroll_element: missing element returns false")
val mgr = scroll_manager_new()
val result = mgr.scroll_element(999, 100.0, 100.0)
expect(result).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `00a2a5e8bf26749e936b7a70f2d2d7905d285e9db5791b1cadbde8593024428e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00a2a5e8bf26749e936b7a70f2d2d7905d285e9db5791b1cadbde8593024428e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00a2a5e8bf26749e936b7a70f2d2d7905d285e9db5791b1cadbde8593024428e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/blink/scroll_manager_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/scroll_manager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/scroll_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/scroll_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/scroll_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/scroll_manager_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scroll_x/y start at 0, overflow=Auto' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/scroll_manager_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'max_scroll_x/y: correct for content > viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/scroll_manager_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scroll_by: clamps to max (beyond content does not overshoot)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
