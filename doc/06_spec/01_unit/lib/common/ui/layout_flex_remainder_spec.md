# layout_flex_remainder_spec

> Purpose: Prove that layout_hbox flex remainder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# layout_flex_remainder_spec

Purpose: Prove that layout_hbox flex remainder.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that layout_hbox flex remainder.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### layout_hbox flex remainder

#### never awards the remainder twice — a flex=0 child gets no width

- never awards the remainder twice — a flex=0 child gets no width
- Verify: never awards the remainder twice — a flex=0 child gets no width
   - Expected: b_w equals `0`
   - Expected: a_w equals `10`
   - Expected: a_w + b_w equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never awards the remainder twice — a flex=0 child gets no width")
step("Verify: never awards the remainder twice — a flex=0 child gets no width")
# @req: REQ-LIB-COMMON-001
# REGRESSION: box w=10, A flex=3, B flex=0.
# total_flex=3, flex_unit=3, flex_remainder=10-9=1.
# A: flex_idx 0->3, 3>=3 -> 3*3+1 = 10  (correct)
# B: flex_idx 3->3, 3>=3 -> 0*3+1 = 1   (WRONG: remainder again)
# 10+1 = 11px assigned into a 10px box.
val a = with_flex(label("flexrem_a", "A"), 3)
val b = with_flex(label("flexrem_b", "B"), 0)
val rects = compute_layout(_hbox("flexrem_root", [a, b]), 0, 0, 10, 4)
val a_w = _w(rects, "flexrem_a")
val b_w = _w(rects, "flexrem_b")
expect(b_w).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(a_w).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(a_w + b_w).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### gives all-positive flex children the same geometry as before (control)

- gives all-positive flex children the same geometry as before (control)
- Verify: gives all-positive flex children the same geometry as before (control)
   - Expected: _w(rects, "flexctl_c1") equals `6`
   - Expected: _w(rects, "flexctl_c2") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives all-positive flex children the same geometry as before (control)")
step("Verify: gives all-positive flex children the same geometry as before (control)")
# Discriminating control: no flex=0 child, so the guard change cannot
# move these numbers. Must pass in BOTH directions — a green here with
# a red above proves the oracle discriminates instead of failing
# wholesale.
# total_flex=4, flex_unit=2, remainder=2.
# C1: flex_idx 0->3, 3<4  -> 3*2   = 6
# C2: flex_idx 3->4, 4>=4 -> 1*2+2 = 4
val c1 = with_flex(label("flexctl_c1", "1"), 3)
val c2 = with_flex(label("flexctl_c2", "2"), 1)
val rects = compute_layout(_hbox("flexctl_root", [c1, c2]), 0, 0, 10, 4)
expect(_w(rects, "flexctl_c1")).to_equal(6)
expect(_w(rects, "flexctl_c2")).to_equal(4)
```

</details>

#### treats a NEGATIVE flex as zero instead of double-awarding

- treats a NEGATIVE flex as zero instead of double-awarding
- Verify: treats a NEGATIVE flex as zero instead of double-awarding
   - Expected: w2 equals `0`
   - Expected: w1 + w2 + w3 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats a NEGATIVE flex as zero instead of double-awarding")
step("Verify: treats a NEGATIVE flex as zero instead of double-awarding")
# REGRESSION: `with_flex(node, -2)` and sdn `flex: -2` both parse, and
# a negative weight made flex_idx non-monotone, so more than one child
# could satisfy `flex_idx >= total_flex` even with the flex > 0 guard.
# Unclamped, w=10 with flex 5 / -2 / 1:
#   total_flex = 4, flex_unit = 2, flex_remainder = 2
#   C1: flex_idx 0->5, 5>=4 -> 5*2+2 = 12   (remainder)
#   C2: flex_idx 5->3, flex<0, skipped
#   C3: flex_idx 3->4, 4>=4 -> 1*2+2 = 4    (remainder AGAIN)
#   12+4 = 16px into a 10px box.
# Clamped, total_flex = 6, flex_unit = 1, remainder = 4:
#   C1 -> 5, C2 -> 0 (dropped), C3 -> 1*1+4 = 5. Sum = 10.
val c1 = with_flex(label("flexneg_c1", "1"), 5)
val c2 = with_flex(label("flexneg_c2", "2"), -2)
val c3 = with_flex(label("flexneg_c3", "3"), 1)
val rects = compute_layout(_hbox("flexneg_root", [c1, c2, c3]), 0, 0, 10, 4)
val w1 = _w(rects, "flexneg_c1")
val w2 = _w(rects, "flexneg_c2")
val w3 = _w(rects, "flexneg_c3")
expect(w2).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w1 + w2 + w3).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### was already correct with a LEADING flex=0 child (control)

- was already correct with a LEADING flex=0 child (control)
- Verify: was already correct with a LEADING flex=0 child (control)
   - Expected: _w(rects, "flexlead_b") equals `0`
   - Expected: _w(rects, "flexlead_a") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("was already correct with a LEADING flex=0 child (control)")
step("Verify: was already correct with a LEADING flex=0 child (control)")
# Second control, also unchanged in both directions: with the zero
# child FIRST, flex_idx is still 0 when it is visited, so 0 >= 3 is
# false and the remainder was never double-awarded. This pins that the
# defect was specifically about TRAILING zero-flex children, not about
# flex=0 in general.
val b = with_flex(label("flexlead_b", "B"), 0)
val a = with_flex(label("flexlead_a", "A"), 3)
val rects = compute_layout(_hbox("flexlead_root", [b, a]), 0, 0, 10, 4)
expect(_w(rects, "flexlead_b")).to_equal(0)
expect(_w(rects, "flexlead_a")).to_equal(10)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd265f391a7feb6b13da8b19a2efafdd85e77340ff31e4e94660264182d98d1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd265f391a7feb6b13da8b19a2efafdd85e77340ff31e4e94660264182d98d1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd265f391a7feb6b13da8b19a2efafdd85e77340ff31e4e94660264182d98d1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/layout_flex_remainder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/layout_flex_remainder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/layout_flex_remainder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never awards the remainder twice — a flex=0 child gets no width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives all-positive flex children the same geometry as before (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/layout_flex_remainder_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a NEGATIVE flex as zero instead of double-awarding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
