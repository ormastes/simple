# Containment Layout Contain Wired Specification

> Tests covering CSS contain:layout wired into the real layout_selected hot path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Containment Layout Contain Wired Specification

## Scenarios

### CSS contain:layout wired into the real layout_selected hot path

#### (a) correctness: fast-path recompute (boundary has a fixed size) matches full recompute exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- (a) correctness: fast-path recompute (boundary has a fixed size) matches full recompute exactly
   - Expected: id_a > 0 is true
   - Expected: fast.fault equals ``
   - Expected: boxes_match(fast.layout, full.layout) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) correctness: fast-path recompute (boundary has a fixed size) matches full recompute exactly")
val html1 = html_c_fixed("Short")
val nodes1 = parse_html(html1)
val rules1 = extract_css_vw(html1, WIDTH, false)
val child_index1 = build_child_index(nodes1)
val styles1 = compute_styles(nodes1, rules1, child_index1, false, true)
val retained = layout_selected(nodes1, styles1, child_index1, [1], WIDTH, VIEWPORT_H, empty_retained()).layout

val html2 = html_c_fixed("Much longer text content inside A that changes how it wraps across lines")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val styles2 = compute_styles(nodes2, rules2, child_index2, false, true)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)

val fast = layout_selected(nodes2, styles2, child_index2, [id_a], WIDTH, VIEWPORT_H, retained)
val full = layout_selected(nodes2, styles2, child_index2, [1], WIDTH, VIEWPORT_H, empty_retained())
expect(fast.fault).to_equal("")
expect(boxes_match(fast.layout, full.layout)).to_equal(true)
```

</details>

#### (a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches full recompute

- (a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches full recompute
   - Expected: id_a > 0 is true
   - Expected: fast.fault equals ``
   - Expected: boxes_match(fast.layout, full.layout) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches full recompute")
val html1 = html_c_auto("Short")
val nodes1 = parse_html(html1)
val rules1 = extract_css_vw(html1, WIDTH, false)
val child_index1 = build_child_index(nodes1)
val styles1 = compute_styles(nodes1, rules1, child_index1, false, true)
val retained = layout_selected(nodes1, styles1, child_index1, [1], WIDTH, VIEWPORT_H, empty_retained()).layout

val html2 = html_c_auto("Much longer text content inside A that wraps across several lines and grows the auto-height container c")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val styles2 = compute_styles(nodes2, rules2, child_index2, false, true)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)

val fast = layout_selected(nodes2, styles2, child_index2, [id_a], WIDTH, VIEWPORT_H, retained)
val full = layout_selected(nodes2, styles2, child_index2, [1], WIDTH, VIEWPORT_H, empty_retained())
expect(fast.fault).to_equal("")
expect(boxes_match(fast.layout, full.layout)).to_equal(true)
```

</details>

#### (b) proportionality: a contain:layout boundary bounds the recompute to a strict subtree

- (b) proportionality: a contain:layout boundary bounds the recompute to a strict subtree
   - Expected: id_a > 0 is true
   - Expected: subtree_size < nodes2.len() as i32 is true
   - Expected: subtree_size > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) proportionality: a contain:layout boundary bounds the recompute to a strict subtree")
val html2 = html_c_fixed("Much longer text content inside A that changes how it wraps across lines")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)

val subtree_size = layout_contain_boundary_subtree_size(nodes2, child_index2, [id_a])
expect(subtree_size < nodes2.len() as i32).to_equal(true)
expect(subtree_size > 0).to_equal(true)
```

</details>

#### (b) proportionality: no shared contain:layout boundary reports the full tree (no savings claimed)

- (b) proportionality: no shared contain:layout boundary reports the full tree (no savings claimed)
   - Expected: id_a > 0 is true
   - Expected: id_sibling > 0 is true
   - Expected: subtree_size equals `nodes2.len() as i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) proportionality: no shared contain:layout boundary reports the full tree (no savings claimed)")
val html2 = html_c_fixed("Short")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val id_a = find_structural_id(nodes2, "a")
val id_sibling = find_structural_id(nodes2, "sibling")
expect(id_a > 0).to_equal(true)
expect(id_sibling > 0).to_equal(true)

# "a" is inside the c boundary, "sibling" is not -- no single shared
# boundary covers both, so the fast path must not be claimed.
val subtree_size = layout_contain_boundary_subtree_size(nodes2, child_index2, [id_a, id_sibling])
expect(subtree_size).to_equal(nodes2.len() as i32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSS contain:layout wired into the real layout_selected hot path.
- CSS contain:layout wired into the real layout_selected hot path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `fb6c6265d2f5cdd7168614d5b67929530749908024c9e11d124de5e7b9d74689`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb6c6265d2f5cdd7168614d5b67929530749908024c9e11d124de5e7b9d74689`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb6c6265d2f5cdd7168614d5b67929530749908024c9e11d124de5e7b9d74689`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) correctness: fast-path recompute (boundary has a fixed size) matches full recompute exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches full recompute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_layout_contain_wired_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(b) proportionality: a contain:layout boundary bounds the recompute to a strict subtree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
