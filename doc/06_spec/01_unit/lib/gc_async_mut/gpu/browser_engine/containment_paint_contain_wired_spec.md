# Containment Paint Contain Wired Specification

> Tests covering CSS contain:paint wired into the real paint_selected hot path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Containment Paint Contain Wired Specification

## Scenarios

### CSS contain:paint wired into the real paint_selected hot path

#### (a) correctness: fast-path repaint (boundary box unchanged) is pixel-identical to a full repaint

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- (a) correctness: fast-path repaint (boundary box unchanged) is pixel-identical to a full repaint
   - Expected: id_c1 > 0 is true
   - Expected: id_a > 0 is true
   - Expected: fast.len() equals `full.len()`
   - Expected: diff_count(fast, full) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("(a) correctness: fast-path repaint (boundary box unchanged) is pixel-identical to a full repaint")
val (nodes1, bx1, by1, bw1, bh1, fb1) = render_full(html_c_fixed("Short"))
val id_c1 = find_structural_id(nodes1, "c")
expect(id_c1 > 0).to_equal(true)
val idx_c1 = (id_c1 - 1) as i32
val retained_bw = bw1[idx_c1]
val retained_bh = bh1[idx_c1]

val html2 = html_c_fixed("Much longer text content inside A that changes how it wraps across the contained box")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val styles2 = compute_styles(nodes2, rules2, child_index2, false, true)
val node_count2 = nodes2.len() as i32
val boxes2 = layout(
    nodes2, styles2, child_index2, 0, 0, 0, WIDTH, HEIGHT,
    zero_i32_list(node_count2), zero_i32_list(node_count2),
    zero_i32_list(node_count2), zero_i32_list(node_count2),
    empty_i32_lists(node_count2), empty_i32_lists(node_count2),
    neg_one_i32_list(node_count2)
)
val wrap_cache2 = TextWrapCache(starts: boxes2.wrap_starts, ends: boxes2.wrap_ends)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)

val white = argb(255, 255, 255)
val fresh_fb = browser_layout_framebuffer_filled(white, WIDTH, HEIGHT)
val full = paint(nodes2, styles2, boxes2.bx, boxes2.by, boxes2.bw, boxes2.bh, wrap_cache2, fresh_fb, WIDTH, HEIGHT, false)

val fast = paint_selected(
    nodes2, styles2, boxes2.bx, boxes2.by, boxes2.bw, boxes2.bh, wrap_cache2,
    fb1, retained_bw, retained_bh, WIDTH, HEIGHT, false, [id_a]
)
expect(fast.len()).to_equal(full.len())
expect(diff_count(fast, full)).to_equal(0)
```

</details>

#### (a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches a full repaint of the same retained buffer

- (a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches a full repaint of the same retained buffer
   - Expected: id_c1 > 0 is true
   - Expected: id_a > 0 is true
   - Expected: boxes2.bh[idx_c2] != retained_bh is true
   - Expected: fast.len() equals `full.len()`
   - Expected: diff_count(fast, full) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("(a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches a full repaint of the same retained buffer")
# This case falls all the way through `paint_selected`'s fallback,
# which -- like the fast path -- draws onto `retained_fb`, not a
# freshly-filled buffer (paint() only overwrites pixels an actual
# node draws; reusing the retained buffer avoids paying for a
# fresh-fill on every mismatch). The oracle below must draw onto
# that SAME starting buffer to isolate "did the fallback draw
# everything a full repaint would" from "did the two runs start
# from different backgrounds" -- confirmed with test 1's fixture:
# a fresh-white oracle only coincidentally matches when the
# document fully covers the canvas.
val (nodes1, bx1, by1, bw1, bh1, fb1) = render_full(html_c_auto("Short"))
val id_c1 = find_structural_id(nodes1, "c")
expect(id_c1 > 0).to_equal(true)
val idx_c1 = (id_c1 - 1) as i32
val retained_bw = bw1[idx_c1]
val retained_bh = bh1[idx_c1]

val html2 = html_c_auto("Much longer text content inside A that wraps across several lines and grows the auto-height container c")
val nodes2 = parse_html(html2)
val rules2 = extract_css_vw(html2, WIDTH, false)
val child_index2 = build_child_index(nodes2)
val styles2 = compute_styles(nodes2, rules2, child_index2, false, true)
val node_count2 = nodes2.len() as i32
val boxes2 = layout(
    nodes2, styles2, child_index2, 0, 0, 0, WIDTH, HEIGHT,
    zero_i32_list(node_count2), zero_i32_list(node_count2),
    zero_i32_list(node_count2), zero_i32_list(node_count2),
    empty_i32_lists(node_count2), empty_i32_lists(node_count2),
    neg_one_i32_list(node_count2)
)
val wrap_cache2 = TextWrapCache(starts: boxes2.wrap_starts, ends: boxes2.wrap_ends)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)
val id_c2 = find_structural_id(nodes2, "c")
val idx_c2 = (id_c2 - 1) as i32
# Sanity: this fixture must actually grow the boundary's box, or the
# test would trivially pass through the fast path instead of
# exercising the fallback guard.
expect(boxes2.bh[idx_c2] != retained_bh).to_equal(true)

val full = paint(nodes2, styles2, boxes2.bx, boxes2.by, boxes2.bw, boxes2.bh, wrap_cache2, fb1, WIDTH, HEIGHT, false)

val fast = paint_selected(
    nodes2, styles2, boxes2.bx, boxes2.by, boxes2.bw, boxes2.bh, wrap_cache2,
    fb1, retained_bw, retained_bh, WIDTH, HEIGHT, false, [id_a]
)
expect(fast.len()).to_equal(full.len())
expect(diff_count(fast, full)).to_equal(0)
```

</details>

#### (b) proportionality: a contain:paint boundary bounds the repaint to a strict subtree

- (b) proportionality: a contain:paint boundary bounds the repaint to a strict subtree
   - Expected: id_a > 0 is true
   - Expected: subtree_size < nodes2.len() as i32 is true
   - Expected: subtree_size > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("(b) proportionality: a contain:paint boundary bounds the repaint to a strict subtree")
val html2 = html_c_fixed("Much longer text content inside A that changes how it wraps across the contained box")
val nodes2 = parse_html(html2)
val id_a = find_structural_id(nodes2, "a")
expect(id_a > 0).to_equal(true)

val subtree_size = paint_contain_boundary_subtree_size(nodes2, [id_a])
expect(subtree_size < nodes2.len() as i32).to_equal(true)
expect(subtree_size > 0).to_equal(true)
```

</details>

#### (b) proportionality: no shared contain:paint boundary reports the full tree (no savings claimed)

- (b) proportionality: no shared contain:paint boundary reports the full tree (no savings claimed)
   - Expected: id_a > 0 is true
   - Expected: id_sibling > 0 is true
   - Expected: subtree_size equals `nodes2.len() as i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("(b) proportionality: no shared contain:paint boundary reports the full tree (no savings claimed)")
val html2 = html_c_fixed("Short")
val nodes2 = parse_html(html2)
val id_a = find_structural_id(nodes2, "a")
val id_sibling = find_structural_id(nodes2, "sibling")
expect(id_a > 0).to_equal(true)
expect(id_sibling > 0).to_equal(true)

# "a" is inside the c boundary, "sibling" is not -- no single shared
# boundary covers both, so the fast path must not be claimed.
val subtree_size = paint_contain_boundary_subtree_size(nodes2, [id_a, id_sibling])
expect(subtree_size).to_equal(nodes2.len() as i32)
```

</details>

#### (b) proportionality: two DIFFERENT contain:paint boundaries in one dirty set also report the full tree

- (b) proportionality: two DIFFERENT contain:paint boundaries in one dirty set also report the full tree
   - Expected: id_a1 > 0 is true
   - Expected: id_a2 > 0 is true
   - Expected: subtree_size equals `nodes3.len() as i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("(b) proportionality: two DIFFERENT contain:paint boundaries in one dirty set also report the full tree")
val html3 = html_two_boundaries()
val nodes3 = parse_html(html3)
val id_a1 = find_structural_id(nodes3, "a1")
val id_a2 = find_structural_id(nodes3, "a2")
expect(id_a1 > 0).to_equal(true)
expect(id_a2 > 0).to_equal(true)

val subtree_size = paint_contain_boundary_subtree_size(nodes3, [id_a1, id_a2])
expect(subtree_size).to_equal(nodes3.len() as i32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSS contain:paint wired into the real paint_selected hot path.
- CSS contain:paint wired into the real paint_selected hot path

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

- Canonical SPipe generation for source `0b00729ae4838253050dc6d866120ac5a3a50210131bbd48a4f6e2f52d8fb9bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b00729ae4838253050dc6d866120ac5a3a50210131bbd48a4f6e2f52d8fb9bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b00729ae4838253050dc6d866120ac5a3a50210131bbd48a4f6e2f52d8fb9bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) correctness: fast-path repaint (boundary box unchanged) is pixel-identical to a full repaint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) correctness: guard rejects a fast path whose boundary box changed (auto-height), still matches a full repaint of the same retained buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_paint_contain_wired_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(b) proportionality: a contain:paint boundary bounds the repaint to a strict subtree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
