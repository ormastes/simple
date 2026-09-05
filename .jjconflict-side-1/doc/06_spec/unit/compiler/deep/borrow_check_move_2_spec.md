# borrow_check_move_2_spec

> Borrow-checker move revival granularity + false-positive avoidance

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrow_check_move_2_spec

Borrow-checker move revival granularity + false-positive avoidance

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/deep/borrow_check_move_2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Borrow-checker move revival granularity + false-positive avoidance
(lane SF1, 2026-07-28).

BorrowGraph.record_assign kills forward-propagated moved state so a
re-initialized place is usable again, but the kill is scoped by whether
the WRITE is a whole-local write or a projected (field) write:
  - a whole-local write (`place.projections.len() == 0`) revives the
    local and everything under it (place_base_equals on the base alone);
  - a projected write revives only the EXACT place it targets
    (place_equals, full path match).
That asymmetry is the part most likely to regress silently, so it gets
dedicated coverage here alongside the MIR-level Copy/Const/Assign wiring
in borrow_check/mod.spl (each of those instruction kinds must record an
ASSIGN of its destination, never a USE — recording a use would flag
ordinary re-initialization as use-after-move).

## Scenarios

### BorrowGraph move revival — whole-local vs projected writes

#### a whole-local reassign revives a previously-moved FIELD

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a whole-local reassign revives a previously-moved FIELD


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a whole-local reassign revives a previously-moved FIELD")
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, field0)
graph.record_assign(5, whole)
graph.record_use(7, field0)
assert_false(graph.has_errors())
```

</details>

#### a projected (field) reassign does NOT revive the whole moved local

- a projected (field) reassign does NOT revive the whole moved local


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a projected (field) reassign does NOT revive the whole moved local")
# Writing only x.f0 must not make a later read of plain `x` look
# safe -- the rest of x may still be moved-out.
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, whole)
graph.record_assign(5, field0)
graph.record_use(7, whole)
assert_true(graph.has_errors())
```

</details>

#### a projected (field) reassign DOES revive that exact field

- a projected (field) reassign DOES revive that exact field


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a projected (field) reassign DOES revive that exact field")
# Here the MOVE itself targets the field (not the whole local), so
# the field-projected reassign is an EXACT place_equals match
# against the moved entry and kills it.
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, field0)
graph.record_assign(5, field0)
graph.record_use(7, field0)
assert_false(graph.has_errors())
```

</details>

#### reassignment kills moved state (re-init revives the place)

- reassignment kills moved state (re-init revives the place)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassignment kills moved state (re-init revives the place)")
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
graph.record_assign(5, p)
graph.record_use(7, p)
assert_false(graph.has_errors())
```

</details>

#### does not flag use of a different local after a move

- does not flag use of a different local after a move


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag use of a different local after a move")
var graph = BorrowGraph.create()
graph.record_move(3, Place.local(0))
graph.record_use(7, Place.local(1))
assert_false(graph.has_errors())
```

</details>

### BorrowChecker MIR wiring — Copy/Const/Assign never record a USE

#### Copy's destination is reinitialized, not used: no false positive

- Copy's destination is reinitialized, not used: no false positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Copy's destination is reinitialized, not used: no false positive")
# Move(l1, l0) moves l0. Copy(l0, l2) then writes INTO l0 (dest),
# reinitializing it -- if the Copy case wrongly recorded a USE of
# its destination this would false-positive as use-after-move.
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val l2 = LocalId(id: 2)
val l3 = LocalId(id: 3)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0)),
    mk_inst(MirInstKind.Copy(l0, l2)),
    mk_inst(MirInstKind.Copy(l3, l0))
]
assert_false(body_has_errors(insts))
```

</details>

#### Const rewrite of a moved-out local is not a false positive

- Const rewrite of a moved-out local is not a false positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Const rewrite of a moved-out local is not a false positive")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val l2 = LocalId(id: 2)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0)),
    mk_inst(MirInstKind.Const(l0, MirConstValue.Int(9), MirType.i64())),
    mk_inst(MirInstKind.Copy(l2, l0))
]
assert_false(body_has_errors(insts))
```

</details>

#### still detects use-after-move when no reinitialization occurs

- still detects use-after-move when no reinitialization occurs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still detects use-after-move when no reinitialization occurs")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val l2 = LocalId(id: 2)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0)),
    mk_inst(MirInstKind.Copy(l2, l0))
]
assert_true(body_has_errors(insts))
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fd85cdd8073858c3c16acf706cde132ce2b0f0a456fae0909232f677d529c85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fd85cdd8073858c3c16acf706cde132ce2b0f0a456fae0909232f677d529c85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fd85cdd8073858c3c16acf706cde132ce2b0f0a456fae0909232f677d529c85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/deep/borrow_check_move_2_spec.spl
mirror: doc/06_spec/unit/compiler/deep/borrow_check_move_2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/deep/borrow_check_move_2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/deep/borrow_check_move_2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/deep/borrow_check_move_2_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a whole-local reassign revives a previously-moved FIELD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/deep/borrow_check_move_2_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a projected (field) reassign does NOT revive the whole moved local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/deep/borrow_check_move_2_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a projected (field) reassign DOES revive that exact field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
