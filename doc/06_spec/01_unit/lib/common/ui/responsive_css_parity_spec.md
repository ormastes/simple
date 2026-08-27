# Responsive Css Parity Specification

> Tests covering responsive_css — single-source breakpoints, boundary parity with classify().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Responsive Css Parity Specification

## Scenarios

### responsive_css — single-source breakpoints, boundary parity with classify()

#### default_breakpoints compact query uses compact_max-1 as max-width

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default_breakpoints compact query uses compact_max-1 as max-width


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_breakpoints compact query uses compact_max-1 as max-width")
val bp = default_breakpoints()
val css = responsive_css(bp)
val compact_edge = bp.compact_max - 1
val expected = "@media (max-width: {compact_edge}px)"
expect(css).to_contain(expected)
```

</details>

#### default_breakpoints regular query uses compact_max as min-width and regular_max-1 as max-width

- default_breakpoints regular query uses compact_max as min-width and regular_max-1 as max-width


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_breakpoints regular query uses compact_max as min-width and regular_max-1 as max-width")
val bp = default_breakpoints()
val css = responsive_css(bp)
val compact_min = bp.compact_max
val regular_edge = bp.regular_max - 1
val expected = "@media (min-width: {compact_min}px) and (max-width: {regular_edge}px)"
expect(css).to_contain(expected)
```

</details>

#### custom breakpoints (700/1000) produces correct boundary strings

- custom breakpoints (700/1000) produces correct boundary strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom breakpoints (700/1000) produces correct boundary strings")
val bp = Breakpoints(compact_max: 700, regular_max: 1000)
val css = responsive_css(bp)
expect(css).to_contain("699px")
expect(css).to_contain("700px")
expect(css).to_contain("999px")
```

</details>

#### custom breakpoints (700/1000) does not contain stale default compact boundary

- custom breakpoints (700/1000) does not contain stale default compact boundary
   - Expected: css does not contain `(max-width: 600px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom breakpoints (700/1000) does not contain stale default compact boundary")
val bp = Breakpoints(compact_max: 700, regular_max: 1000)
val css = responsive_css(bp)
# 600 should not appear as a max-width media boundary when compact_max is 700
expect(css.contains("(max-width: 600px)")).to_equal(false)
```

</details>

#### stale-literal guard: default breakpoints CSS contains the regular_max-1 boundary, not 1200

- stale-literal guard: default breakpoints CSS contains the regular_max-1 boundary, not 1200
   - Expected: css does not contain `(max-width: 1200px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stale-literal guard: default breakpoints CSS contains the regular_max-1 boundary, not 1200")
val bp = default_breakpoints()
val css = responsive_css(bp)
val regular_edge = bp.regular_max - 1
# CSS must contain the derived regular boundary
val expected = "{regular_edge}px"
expect(css).to_contain(expected)
# And must not contain stale 1200 unless regular_max IS 1201
# (if regular_max changed from 1200 to 840, then "1200" must not appear as a boundary)
if bp.regular_max != 1201:
    expect(css.contains("(max-width: 1200px)")).to_equal(false)
```

</details>

#### generate_css feeds default_breakpoints into responsive_css (compact query present)

- generate_css feeds default_breakpoints into responsive_css (compact query present)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generate_css feeds default_breakpoints into responsive_css (compact query present)")
val bp = default_breakpoints()
val compact_edge = bp.compact_max - 1
val expected = "@media (max-width: {compact_edge}px)"
val css = generate_css("modern")
expect(css).to_contain(expected)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/responsive_css_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering responsive_css — single-source breakpoints, boundary parity with classify().
- responsive_css — single-source breakpoints, boundary parity with classify()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d8db5db56e83314d8cc07b55ca3b925de87a8733bba3251f72ef9e6fffd25439`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8db5db56e83314d8cc07b55ca3b925de87a8733bba3251f72ef9e6fffd25439`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8db5db56e83314d8cc07b55ca3b925de87a8733bba3251f72ef9e6fffd25439`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/responsive_css_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/responsive_css_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/responsive_css_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/responsive_css_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/responsive_css_parity_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_breakpoints compact query uses compact_max-1 as max-width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/responsive_css_parity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_breakpoints regular query uses compact_max as min-width and regular_max-1 as max-width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/responsive_css_parity_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'custom breakpoints (700/1000) produces correct boundary strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
