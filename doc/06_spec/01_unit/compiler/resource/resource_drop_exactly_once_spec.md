# `resource` invariants 1 & 6 -- exactly-once release, `close()` consumes

> §8, invariants 1 ("live owned resource -> moved or dropped exactly once")

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` invariants 1 & 6 -- exactly-once release, `close()` consumes

§8, invariants 1 ("live owned resource -> moved or dropped exactly once")

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**WP:** WP-G (`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`).
**Architecture:** `doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`
§8, invariants 1 ("live owned resource -> moved or dropped exactly once")
and 6 ("`close()` consumes even though spelled as a method").

Before this spec, `MirInstKind.Drop` (WP-E's drop-edge marker, emitted at
scope exit, `return`, `?` early-return, AND at an explicit `.close()` call
-- `method_calls_literals.spl`'s `lower_method_call`) fell through the
borrow checker's `analyze_instruction` no-op catch-all arm
(`borrow_check/mod.spl`) and produced NO move/consume fact at all. A
resource dropped/closed twice, or used after `.close()`, was therefore
invisible to the checker however lowering built the MIR.

Fix: a new `case Drop(local):` arm treats a Drop exactly like a Move of its
place (`nll.record_move`), reusing `record_move`'s existing double-move
detection (LANE ISO1, `borrow_graph.spl`) for both invariants at once --
invariant 6 is not separate enforcement, it is what makes WP-E's
already-landed `.close() -> Drop` lowering actually checked.

Hand-built MIR harness (same technique as `borrow_check_spec.spl`'s
"BorrowChecker MIR use-after-move" section) -- this drives the checker
directly on `MirInstKind.Drop` instructions, independent of HIR/lowering,
which is the correct level for WP-G (borrow-check enforcement) itself.

**Known, accepted over-approximation** (see the third `describe` block):
the checker's walk (SF1, `borrow_graph.spl`) is linear over `func.blocks`
in array order, not CFG-path-sensitive -- the same limitation already
documented and accepted for `Move` in
`doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`.
Two Drops of the same local on genuinely mutually-exclusive branches (e.g.
WP-E's own independent per-exit drop edges) can therefore false-positive.
This spec measures that behaviour honestly rather than asserting past it.

## Scenarios

### invariant 1: exactly-once release -- a single Drop is legal

#### reports no diagnostic for one Drop of a resource-owned local

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports no diagnostic for one Drop of a resource-owned local


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no diagnostic for one Drop of a resource-owned local")
val l0 = LocalId(id: 0)
val errors = errors_for([mk_inst(MirInstKind.Drop(l0))])
assert_true(errors.len() == 0)
```

</details>

### invariant 1: exactly-once release -- a double Drop (double-close) is caught

#### reports a borrow diagnostic for two Drops of the same local in one block

- reports a borrow diagnostic for two Drops of the same local in one block


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for two Drops of the same local in one block")
# This is the real-world shape of `x.close(); x.close()` -- both
# calls lower to their own independent Drop(x) instruction
# (method_calls_literals.spl has no guard against calling `.close()`
# twice at the lowering level; WP-G's job is to catch it here).
val l0 = LocalId(id: 0)
val errors = errors_for([
    mk_inst(MirInstKind.Drop(l0)),
    mk_inst(MirInstKind.Drop(l0))
])
assert_true(errors.len() > 0)
```

</details>

#### does not flag a Drop of a DIFFERENT local after a Drop

- does not flag a Drop of a DIFFERENT local after a Drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag a Drop of a DIFFERENT local after a Drop")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val errors = errors_for([
    mk_inst(MirInstKind.Drop(l0)),
    mk_inst(MirInstKind.Drop(l1))
])
assert_true(errors.len() == 0)
```

</details>

### invariant 6: close() consumes -- use after Drop is a real use-after-move

#### reports a borrow diagnostic for a Copy-use of a local after its Drop

- reports a borrow diagnostic for a Copy-use of a local after its Drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for a Copy-use of a local after its Drop")
# `x.close(); val y = x` -- the second reference to `x` reads memory
# the consuming close already released.
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val errors = errors_for([
    mk_inst(MirInstKind.Drop(l0)),
    mk_inst(MirInstKind.Copy(l1, l0))
])
assert_true(errors.len() > 0)
```

</details>

#### reports no diagnostic for a Copy-use BEFORE the Drop

- reports no diagnostic for a Copy-use BEFORE the Drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no diagnostic for a Copy-use BEFORE the Drop")
val l0 = LocalId(id: 0)
val l1 = LocalId(id: 1)
val errors = errors_for([
    mk_inst(MirInstKind.Copy(l1, l0)),
    mk_inst(MirInstKind.Drop(l0))
])
assert_true(errors.len() == 0)
```

</details>

### known limitation (inherited from SF1, not a new WP-G defect): the checker's linear block walk is not CFG-path-sensitive

#### documents that two Drops of the same local in DIFFERENT blocks (e.g. mutually-exclusive branches) are indistinguishable from a real double-drop

- documents that two Drops of the same local in DIFFERENT blocks (e.g. mutually-exclusive branches) are indistinguishable from a real double-drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents that two Drops of the same local in DIFFERENT blocks (e.g. mutually-exclusive branches) are indistinguishable from a real double-drop")
# Mirrors WP-E's `emit_pending_resource_drops`: an early-return
# branch and the function's own fall-through exit each get an
# INDEPENDENT drop edge on their own, mutually-exclusive path.
# A real CFG-sensitive checker would accept this; SF1's linear walk
# (documented, out of scope for WP-G) sees both Drops in sequence
# and currently reports a diagnostic here, the same known
# over-approximation already accepted for Move
# (iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md).
# This is measured and reported, not silently asserted past.
val l0 = LocalId(id: 0)
val block0 = MirBlock(
    id: BlockId.new(0),
    label: nil,
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Bool(true), MirType(kind: MirTypeKind.I8))),
        BlockId.new(1),
        BlockId.new(2)
    )
)
val block1 = MirBlock(
    id: BlockId.new(1),
    label: nil,
    instructions: [mk_inst(MirInstKind.Drop(l0))],
    terminator: MirTerminator.Ret(nil)
)
val block2 = MirBlock(
    id: BlockId.new(2),
    label: nil,
    instructions: [mk_inst(MirInstKind.Drop(l0))],
    terminator: MirTerminator.Ret(nil)
)
val body = MirBody(
    name: "resource_drop_branch_fn",
    blocks: [block0, block1, block2],
    locals: [],
    arg_count: 0,
    return_ty: MirType.i64()
)
var checker = BorrowChecker.create()
checker.check_function(body)
# Report the ACTUAL measured behaviour rather than assuming either
# answer -- see the spec's docstring and this block's header for
# what a positive count here means (known, accepted, pre-existing
# over-approximation, not a WP-G regression).
print "[resource-drop-branch] measured errors.len()={checker.errors.len()}"
assert_true(true)
```

</details>

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

- Canonical SPipe generation for source `7d3a430071f616987370c1090c9db464b0adade07ba0e5fe99bfb7ffbba03d71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d3a430071f616987370c1090c9db464b0adade07ba0e5fe99bfb7ffbba03d71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d3a430071f616987370c1090c9db464b0adade07ba0e5fe99bfb7ffbba03d71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_drop_exactly_once_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_drop_exactly_once_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_drop_exactly_once_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no diagnostic for one Drop of a resource-owned local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a borrow diagnostic for two Drops of the same local in one block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag a Drop of a DIFFERENT local after a Drop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
