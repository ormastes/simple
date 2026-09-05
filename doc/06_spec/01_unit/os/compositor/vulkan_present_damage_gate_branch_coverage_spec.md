# Vulkan Present Damage Gate Branch Coverage Specification

> Tests covering hosted_vulkan_present_rects_valid viewport and mode gates, hosted_vulkan_present_rects_valid FULL canonical rect, hosted_vulkan_present_rects_valid LOCAL per-rect bounds, hosted_vulkan_present_rects_valid LOCAL overlap gate, hosted_vulkan_present_revision_valid, hosted_vulkan_present_identity_valid.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Present Damage Gate Branch Coverage Specification

## Scenarios

### hosted_vulkan_present_rects_valid viewport and mode gates

#### rejects degenerate viewports on either axis

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects degenerate viewports on either axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects degenerate viewports on either axis")
# width <= 0 true side
expect(hosted_vulkan_present_rects_valid(
    0, 80, DAMAGE_PLAN_LOCAL, [0, 0, 1, 1])).to_equal(false)
expect(hosted_vulkan_present_rects_valid(
    -5, 80, DAMAGE_PLAN_LOCAL, [0, 0, 1, 1])).to_equal(false)
# height <= 0 true side (width valid so the second sub-condition decides)
expect(hosted_vulkan_present_rects_valid(
    100, 0, DAMAGE_PLAN_LOCAL, [0, 0, 1, 1])).to_equal(false)
expect(hosted_vulkan_present_rects_valid(
    100, -1, DAMAGE_PLAN_LOCAL, [0, 0, 1, 1])).to_equal(false)
```

</details>

#### rejects any mode that is neither LOCAL nor FULL

- rejects any mode that is neither LOCAL nor FULL


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects any mode that is neither LOCAL nor FULL")
# mode != LOCAL and mode != FULL both true
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_NONE, [0, 0, 100, 80])).to_equal(false)
expect(hosted_vulkan_present_rects_valid(
    100, 80, 99, [0, 0, 100, 80])).to_equal(false)
```

</details>

#### rejects empty, odd-length, and over-budget rect arrays

- rejects empty, odd-length, and over-budget rect arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty, odd-length, and over-budget rect arrays")
# rects.len() == 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [])).to_equal(false)
# rects.len() % 4 != 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [1, 2, 3])).to_equal(false)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [1, 2, 3, 4, 5])).to_equal(false)
# rects.len() / 4 > HOSTED_VULKAN_PRESENT_MAX_RECTS (257 rects)
var too_many: [i64] = []
var count: i64 = 0
while count <= HOSTED_VULKAN_PRESENT_MAX_RECTS:
    # 1x1 rects along the diagonal, all in-bounds and non-overlapping
    too_many.push(count)
    too_many.push(count)
    too_many.push(1)
    too_many.push(1)
    count = count + 1
expect(hosted_vulkan_present_rects_valid(
    1000, 1000, DAMAGE_PLAN_LOCAL, too_many)).to_equal(false)
```

</details>

### hosted_vulkan_present_rects_valid FULL canonical rect

#### accepts only the exact full-viewport rect

- accepts only the exact full-viewport rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only the exact full-viewport rect")
# all four conjuncts true
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL, [0, 0, 100, 80])).to_equal(true)
# rects.len() == 4 false (two rects)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL,
    [0, 0, 100, 80, 0, 0, 1, 1])).to_equal(false)
# rects[0] == 0 false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL, [1, 0, 100, 80])).to_equal(false)
# rects[1] == 0 false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL, [0, 1, 100, 80])).to_equal(false)
# rects[2] == width false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL, [0, 0, 99, 80])).to_equal(false)
# rects[3] == height false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_FULL, [0, 0, 100, 79])).to_equal(false)
```

</details>

### hosted_vulkan_present_rects_valid LOCAL per-rect bounds

#### accepts an in-bounds rect and the full-cover local rect

- accepts an in-bounds rect and the full-cover local rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an in-bounds rect and the full-cover local rect")
# every bounds sub-condition false; loop entered then exits
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, 3, 10, 12])).to_equal(true)
# rect exactly covering the viewport is a legal LOCAL rect
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [0, 0, 100, 80])).to_equal(true)
```

</details>

#### rejects each out-of-bounds axis independently

- rejects each out-of-bounds axis independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects each out-of-bounds axis independently")
# x < 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [-1, 3, 10, 12])).to_equal(false)
# y < 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, -1, 10, 12])).to_equal(false)
# rect_width <= 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, 3, 0, 12])).to_equal(false)
# rect_height <= 0
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, 3, 10, -2])).to_equal(false)
# x >= width
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [100, 3, 1, 1])).to_equal(false)
# y >= height
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, 80, 1, 1])).to_equal(false)
# rect_width > width - x (right edge overflow by one)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [95, 3, 6, 1])).to_equal(false)
# rect_height > height - y (bottom edge overflow by one)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL, [2, 75, 1, 6])).to_equal(false)
```

</details>

### hosted_vulkan_present_rects_valid LOCAL overlap gate

#### rejects overlapping local rects

- rejects overlapping local rects


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping local rects")
# all four overlap conjuncts true
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [2, 3, 10, 12, 9, 12, 5, 3])).to_equal(false)
# containment counts as overlap too
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [0, 0, 50, 50, 10, 10, 5, 5])).to_equal(false)
```

</details>

#### accepts disjoint rects flipping each overlap conjunct

- accepts disjoint rects flipping each overlap conjunct


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts disjoint rects flipping each overlap conjunct")
# second rect fully to the right, edges touching: x < prior_x+prior_width false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [2, 3, 10, 12, 12, 3, 5, 3])).to_equal(true)
# second rect fully to the left: prior_x < x + rect_width false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [50, 3, 10, 12, 2, 3, 5, 3])).to_equal(true)
# second rect fully below, edges touching: y < prior_y+prior_height false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [2, 3, 10, 12, 2, 15, 10, 5])).to_equal(true)
# second rect fully above: prior_y < y + rect_height false
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [2, 40, 10, 12, 2, 3, 10, 5])).to_equal(true)
# three disjoint rects: prior loop iterates more than once per rect
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [0, 0, 5, 5, 20, 0, 5, 5, 40, 0, 5, 5])).to_equal(true)
# third rect overlaps the FIRST prior only (prior loop hit at prior=0)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [0, 0, 5, 5, 20, 0, 5, 5, 3, 3, 5, 5])).to_equal(false)
# third rect overlaps the SECOND prior (prior loop advanced past first)
expect(hosted_vulkan_present_rects_valid(
    100, 80, DAMAGE_PLAN_LOCAL,
    [0, 0, 5, 5, 20, 0, 5, 5, 22, 2, 5, 5])).to_equal(false)
```

</details>

### hosted_vulkan_present_revision_valid

#### requires strict monotonicity of both serial and revision

- requires strict monotonicity of both serial and revision
   - Expected: hosted_vulkan_present_revision_valid(8, 7, 12, 11) is true
   - Expected: hosted_vulkan_present_revision_valid(7, 7, 12, 11) is false
   - Expected: hosted_vulkan_present_revision_valid(6, 7, 12, 11) is false
   - Expected: hosted_vulkan_present_revision_valid(8, 7, 11, 11) is false
   - Expected: hosted_vulkan_present_revision_valid(8, 7, 10, 11) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires strict monotonicity of both serial and revision")
# both strictly greater -> true
expect(hosted_vulkan_present_revision_valid(8, 7, 12, 11)).to_equal(true)
# serial equal -> false
expect(hosted_vulkan_present_revision_valid(7, 7, 12, 11)).to_equal(false)
# serial went backwards -> false
expect(hosted_vulkan_present_revision_valid(6, 7, 12, 11)).to_equal(false)
# revision equal -> false
expect(hosted_vulkan_present_revision_valid(8, 7, 11, 11)).to_equal(false)
# revision went backwards -> false
expect(hosted_vulkan_present_revision_valid(8, 7, 10, 11)).to_equal(false)
```

</details>

### hosted_vulkan_present_identity_valid

#### rejects non-positive candidate identities

- rejects non-positive candidate identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-positive candidate identities")
# framebuffer <= 0
expect(hosted_vulkan_present_identity_valid(
    0, 5, 6, 0, 0, 0)).to_equal(false)
# device_identity <= 0
expect(hosted_vulkan_present_identity_valid(
    4, -1, 6, 0, 0, 0)).to_equal(false)
# adapter_identity <= 0
expect(hosted_vulkan_present_identity_valid(
    4, 5, 0, 0, 0, 0)).to_equal(false)
```

</details>

#### accepts first-frame zero bindings and exact rebinds

- accepts first-frame zero bindings and exact rebinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts first-frame zero bindings and exact rebinds")
# all bound zero (first frame) -> true
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 0, 0, 0)).to_equal(true)
# all bound match exactly -> true
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 4, 5, 6)).to_equal(true)
# partially bound tuple (mixed zero and matching) -> rejected: the
# identity binds as a whole tuple, so a partial binding must never
# act as a per-component wildcard
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 0, 5, 6)).to_equal(false)
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 4, 0, 6)).to_equal(false)
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 4, 5, 0)).to_equal(false)
```

</details>

#### rejects any bound identity mismatch

- rejects any bound identity mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects any bound identity mismatch")
# bound framebuffer differs
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 9, 5, 6)).to_equal(false)
# bound device differs
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 4, 9, 6)).to_equal(false)
# bound adapter differs
expect(hosted_vulkan_present_identity_valid(
    4, 5, 6, 4, 5, 9)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted_vulkan_present_rects_valid viewport and mode gates, hosted_vulkan_present_rects_valid FULL canonical rect, hosted_vulkan_present_rects_valid LOCAL per-rect bounds, hosted_vulkan_present_rects_valid LOCAL overlap gate, hosted_vulkan_present_revision_valid, hosted_vulkan_present_identity_valid.
- hosted_vulkan_present_rects_valid viewport and mode gates
- hosted_vulkan_present_rects_valid FULL canonical rect
- hosted_vulkan_present_rects_valid LOCAL per-rect bounds
- hosted_vulkan_present_rects_valid LOCAL overlap gate
- hosted_vulkan_present_revision_valid
- hosted_vulkan_present_identity_valid

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `0e174b4f69f16a61958f1f98719886913842e9138a687670ec4df5a6d5663442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e174b4f69f16a61958f1f98719886913842e9138a687670ec4df5a6d5663442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e174b4f69f16a61958f1f98719886913842e9138a687670ec4df5a6d5663442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects degenerate viewports on either axis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects any mode that is neither LOCAL nor FULL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty, odd-length, and over-budget rect arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
