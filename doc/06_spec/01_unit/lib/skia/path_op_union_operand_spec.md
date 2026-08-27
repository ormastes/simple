# path_op Union must include BOTH operands

> Regression + detection specs for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# path_op Union must include BOTH operands

Regression + detection specs for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/path_op_union_operand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression + detection specs for
`doc/08_tracking/bug/skia_path_op_boolean_algorithm_2026-07-20.md`.

(a) reproducing spec: `_path_op_rects` computed rect B's subpath and threw the
    returned `SkPath` away (`_emit_rect(result_path, b...)` with no
    assignment — `SkPath` is immutable/value-returning), so Union always
    produced rect A alone: bbox [0,0,10,10] instead of [0,0,15,15], and the
    disjoint case never contained B's centre.
(b) detection spec: generalises the class — for every binary op, the result
    must depend on BOTH operands. Swapping the operand order of a symmetric
    op (Union, Intersect, Xor) must not change point membership; an op that
    silently drops one operand fails this immediately.

## Scenarios

### path_op Union covers both operands

#### union of two overlapping rects spans the outer union bbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### union of two disjoint rects contains both centres and not the gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = path_op(_rect(0.0, 0.0, 4.0, 4.0), _rect(10.0, 10.0, 14.0, 14.0), PathOp.Union)
expect(u.contains(2.0, 2.0)).to_equal(true)
expect(u.contains(12.0, 12.0)).to_equal(true)
expect(u.contains(7.0, 7.0)).to_equal(false)
```

</details>

### path_op operand symmetry (detection)

#### symmetric ops give the same membership with the operands swapped

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(5.0, 5.0, 15.0, 15.0)
val probes_x = [2.0, 7.0, 12.0, 20.0]
val probes_y = [2.0, 7.0, 12.0, 20.0]
var mismatches = 0
for op in [PathOp.Union, PathOp.Intersect, PathOp.Xor]:
    val ab = path_op(a, b, op)
    val ba = path_op(b, a, op)
    var i = 0
    while i < probes_x.len():
        if ab.contains(probes_x[i], probes_y[i]) != ba.contains(probes_x[i], probes_y[i]):
            mismatches = mismatches + 1
        i = i + 1
expect(mismatches).to_equal(0)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11ef3b8a6dd1b892a31b0ad139b47dbdd27039921ad637469059e1d535d22237`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11ef3b8a6dd1b892a31b0ad139b47dbdd27039921ad637469059e1d535d22237`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11ef3b8a6dd1b892a31b0ad139b47dbdd27039921ad637469059e1d535d22237`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/skia/path_op_union_operand_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/path_op_union_operand_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/path_op_union_operand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/path_op_union_operand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/path_op_union_operand_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/skia/path_op_union_operand_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/path_op_union_operand_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'union of two overlapping rects spans the outer union bbox' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/skia/path_op_union_operand_spec.spl:47:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'union of two disjoint rects contains both centres and not the gap' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/skia/path_op_union_operand_spec.spl:55:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'symmetric ops give the same membership with the operands swapped' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
