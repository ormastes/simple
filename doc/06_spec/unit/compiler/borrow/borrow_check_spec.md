# borrow_check_spec

> Borrow-checker move tracking — honest specs (lane SF1, 2026-07-28).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrow_check_spec

Borrow-checker move tracking — honest specs (lane SF1, 2026-07-28).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/borrow/borrow_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Borrow-checker move tracking — honest specs (lane SF1, 2026-07-28).

Reproduce-first coverage for the starved-checker defects:
(b) `moved_places` was keyed by program point and only read at the SAME
    point — a move at pt3 + use at pt7 was undetectable by construction.
    Fixed by forward-propagated moved state with kill-on-reassignment
    (BorrowGraph.moved_now).
(a) `MirInstKind.Move` had zero emitters; the checker's Move path is
    proven here with hand-built MIR (Simple's surface language has no
    semantically-true move sites today — assignment is copy for value
    types and reference-share for classes; `iso` move-only transfer is
    planned but erased at HIR type lowering).

## Scenarios

### BorrowGraph move dataflow

#### detects use-after-move at the same program point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects use-after-move at the same program point


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use-after-move at the same program point")
# Guard: same-point detection worked before the dataflow fix and
# must keep working after it.
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
graph.record_use(3, p)
assert_true(graph.has_errors())
```

</details>

#### detects use-after-move at a LATER program point

- detects use-after-move at a LATER program point


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use-after-move at a LATER program point")
# Defect (b) reproduction: RED before the moved-state forward
# propagation fix — a move at pt3 + use at pt7 produced no error.
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
graph.record_use(7, p)
assert_true(graph.has_errors())
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

#### detects borrow-of-moved at a later program point

- detects borrow-of-moved at a later program point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects borrow-of-moved at a later program point")
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
val b = graph.record_borrow(7, p, BorrowKind.Shared)
assert_false(b.?)
assert_true(graph.has_errors())
```

</details>

#### assigns borrow identities globally across program points

- assigns borrow identities globally across program points


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns borrow identities globally across program points")
var graph = BorrowGraph.create()
val first = graph.record_borrow(2, Place.local(0), BorrowKind.Shared)
val second = graph.record_borrow(7, Place.local(1), BorrowKind.Shared)
assert_true(first.?)
assert_true(second.?)
assert_true(first.unwrap().id != second.unwrap().id)
```

</details>

### BorrowChecker MIR use-after-move

#### checks conflicting borrows in a non-entry successor block

- checks conflicting borrows in a non-entry successor block


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks conflicting borrows in a non-entry successor block")
# Regression: analysis emitted global points 2/3 for block 1 while
# NLL checked synthetic points 1000/1001; successors were also empty,
# so reverse postorder never visited the block.
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val l2 = LocalId(id: 2)
val entry = MirBlock(id: BlockId.new(0), label: nil,
    instructions: [], terminator: MirTerminator.Goto(BlockId.new(1)))
val successor = MirBlock(id: BlockId.new(1), label: nil,
    instructions: [
        mk_inst(MirInstKind.Ref(l1, MirBorrowKind.Shared,
            MirPlace.local_place(l0))),
        mk_inst(MirInstKind.Ref(l2, MirBorrowKind.Mutable,
            MirPlace.local_place(l0)))
    ], terminator: MirTerminator.Ret(nil))
assert_true(branching_body_has_errors([entry, successor]))
```

</details>

#### errors on Move followed by a later use of the source

- errors on Move followed by a later use of the source


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors on Move followed by a later use of the source")
# Defect (a)/(b) end-to-end at the checker API: hand-built MIR with
# an explicit Move then a Copy USE of the moved source at a later
# instruction (= later program point).
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

#### accepts use of the source after re-initialization

- accepts use of the source after re-initialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts use of the source after re-initialization")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val l2 = LocalId(id: 2)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0)),
    mk_inst(MirInstKind.Const(l0, MirConstValue.Int(1), MirType.i64())),
    mk_inst(MirInstKind.Copy(l2, l0))
]
assert_false(body_has_errors(insts))
```

</details>

#### accepts plain copies with no move involved

- accepts plain copies with no move involved


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts plain copies with no move involved")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val insts = [
    mk_inst(MirInstKind.Const(l0, MirConstValue.Int(7), MirType.i64())),
    mk_inst(MirInstKind.Copy(l1, l0)),
    mk_inst(MirInstKind.Copy(l1, l0))
]
assert_false(body_has_errors(insts))
```

</details>

#### errors on Move followed by returning the moved source (Ret terminator)

- errors on Move followed by returning the moved source (Ret terminator)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors on Move followed by returning the moved source (Ret terminator)")
# Terminator-borrows gap, half (b): the block-instruction loop in
# analyze_mir_borrows never looked at mir_block.terminator, so
# `return x` after moving `x` produced no use-fact at all. This is
# the reproduction for `analyze_terminator`'s `Ret` arm.
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0))
]
val term = MirTerminator.Ret(mir_operand_copy(l0))
assert_true(body_has_errors_with_terminator(insts, term))
```

</details>

#### accepts returning a re-initialized local after a move (Ret terminator)

- accepts returning a re-initialized local after a move (Ret terminator)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts returning a re-initialized local after a move (Ret terminator)")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0)),
    mk_inst(MirInstKind.Const(l0, MirConstValue.Int(1), MirType.i64()))
]
val term = MirTerminator.Ret(mir_operand_copy(l0))
assert_false(body_has_errors_with_terminator(insts, term))
```

</details>

#### accepts returning a different local after a move (Ret terminator)

- accepts returning a different local after a move (Ret terminator)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts returning a different local after a move (Ret terminator)")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val insts = [
    mk_inst(MirInstKind.Move(l1, l0))
]
val term = MirTerminator.Ret(mir_operand_copy(l1))
assert_false(body_has_errors_with_terminator(insts, term))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `fd7f49d108e1b9d0faa3aa848f8e79755843d08f52979cfa3dc38396d3c2088e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd7f49d108e1b9d0faa3aa848f8e79755843d08f52979cfa3dc38396d3c2088e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd7f49d108e1b9d0faa3aa848f8e79755843d08f52979cfa3dc38396d3c2088e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/borrow/borrow_check_spec.spl
mirror: doc/06_spec/unit/compiler/borrow/borrow_check_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/borrow/borrow_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/borrow/borrow_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/borrow/borrow_check_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects use-after-move at the same program point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/borrow/borrow_check_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects use-after-move at a LATER program point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/borrow/borrow_check_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassignment kills moved state (re-init revives the place)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
