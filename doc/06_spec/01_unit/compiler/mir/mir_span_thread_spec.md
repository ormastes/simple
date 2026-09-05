# MIR Per-Instruction Span Threading Specification

> Before this change, every `emit_*` helper on `MirBuilder` (`src/compiler/50.mir/mir_data.spl`) hardcoded `span: nil` on the `MirInst` it built, so no MIR instruction ever carried a real source location -- the missing input for debugger line maps, replay locations, coverage, and per-instruction DWARF `!dbg` emission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Per-Instruction Span Threading Specification

Before this change, every `emit_*` helper on `MirBuilder` (`src/compiler/50.mir/mir_data.spl`) hardcoded `span: nil` on the `MirInst` it built, so no MIR instruction ever carried a real source location -- the missing input for debugger line maps, replay locations, coverage, and per-instruction DWARF `!dbg` emission.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Compiler / MIR |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_span_thread_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Before this change, every `emit_*` helper on `MirBuilder`
(`src/compiler/50.mir/mir_data.spl`) hardcoded `span: nil` on the `MirInst`
it built, so no MIR instruction ever carried a real source location -- the
missing input for debugger line maps, replay locations, coverage, and
per-instruction DWARF `!dbg` emission.

`MirBuilder` now carries a `current_span: Span?` field, seeded per-function
from `begin_function`'s span, and pushed/popped by save-set-restore
wrappers around `lower_stmt` (`mir_lowering_stmts.spl`) and `lower_expr`
(`_MirLoweringExpr/expr_dispatch.spl`) using each HIR node's own `.span`.

## Why this builds HIR by hand instead of parsing source text

An earlier version of this spec drove the real `parse_full_frontend` ->
`HirLowering` -> `MirLowering` pipeline on a small in-memory source string
and asserted on the resulting spans. That test is RED even after this
change: `HirFunction.span` (and every statement/expression span reachable
from it) comes back as the exact zero value `Span(start:0,end:0,line:0,
col:0)` for that pipeline entry point -- i.e. the AST/HIR front-end does
not populate real per-node spans on this path at all. That is a pre-existing
gap in the parser/AST layer, upstream of anything `mir_data.spl` or its
lowering callers touch, and is out of DS5's owned scope
(`src/compiler/50.mir/**`). It has been left as a follow-up rather than
silently worked around here (see the tracking note at the bottom of this
file).

To prove DS5's own mechanism -- that a real (non-nil) span attached to a
HIR node survives into the corresponding MIR instruction, and that a
compound node gets ITS OWN span back (not its last-lowered child's span)
-- this spec builds a small HIR module directly, using hand-chosen,
mutually distinct span line numbers on: two integer-literal leaves, the
inner `Binary` node combining them, a third literal, and the outer
`Binary` node combining the inner result with the third literal. This
isolates the lowering-side threading from the (separately broken) span
computation upstream.

## Scenarios

### MIR instructions carry real per-instruction source spans (DS5)

#### gives each hand-spanned HIR leaf its OWN span in the lowered MIR, and gives each compound Binary node ITS OWN span back rather than its last-lowered operand's

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives each hand-spanned HIR leaf its OWN span in the lowered MIR, and gives each compound Binary node ITS OWN span back rather than its last-lowered operand's
   - Expected: fns.len() > 0 is true
   - Expected: const1_has_span is true
   - Expected: const1_line equals `10`
   - Expected: const2_has_span is true
   - Expected: const2_line equals `20`
   - Expected: const3_has_span is true
   - Expected: const3_line equals `40`
   - Expected: binop_lines.len() equals `2`
   - Expected: binop_lines[0] equals `30`
   - Expected: binop_lines[1] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives each hand-spanned HIR leaf its OWN span in the lowered MIR, and gives each compound Binary node ITS OWN span back rather than its last-lowered operand's")
val hir_module = make_hir_module()
var mir_lowering = MirLowering.new(hir_module.symbols)
val mir_module = mir_lowering.lower_module(hir_module)

val fns = mir_module.functions.values()
expect(fns.len() > 0).to_equal(true)
val mir_fn = fns[0]

var const1_line: i64 = -1
var const1_has_span = false
var const2_line: i64 = -1
var const2_has_span = false
var const3_line: i64 = -1
var const3_has_span = false
var binop_lines: [i64] = []

for block in mir_fn.blocks:
    for inst in block.instructions:
        match inst.kind:
            case MirInstKind.Const(_, value, _):
                match value:
                    case MirConstValue.Int(n):
                        if n == 1:
                            if val sp = inst.span:
                                const1_has_span = true
                                const1_line = sp.line
                        if n == 2:
                            if val sp = inst.span:
                                const2_has_span = true
                                const2_line = sp.line
                        if n == 3:
                            if val sp = inst.span:
                                const3_has_span = true
                                const3_line = sp.line
                    case _:
                        nil
            case MirInstKind.BinOp(_, _, _, _):
                if val sp = inst.span:
                    binop_lines = binop_lines.push(sp.line)
            case _:
                nil

# Leaves: each integer-literal Const must carry its OWN hand-chosen
# span line, not nil and not another leaf's line.
expect(const1_has_span).to_equal(true)
expect(const1_line).to_equal(10)
expect(const2_has_span).to_equal(true)
expect(const2_line).to_equal(20)
expect(const3_has_span).to_equal(true)
expect(const3_line).to_equal(40)

# Compound nodes: exactly 2 BinOp instructions (inner then outer, in
# lowering/emission order -- operands are lowered before the node's
# own instruction is emitted). The inner Binary must read back its
# OWN span (30), not operand 2's span (20) it just finished
# recursing through. The outer Binary must read back ITS OWN span
# (50), not the inner result's span (30) or literal 3's span (40).
# This is exactly the case the lower_expr save/restore wrapper
# exists for: a broken (non-stacking) implementation would leak the
# last-processed child's span into the parent's own instruction.
expect(binop_lines.len()).to_equal(2)
expect(binop_lines[0]).to_equal(30)
expect(binop_lines[1]).to_equal(50)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `e923eb9ccd2d25e10956de8fd6fd7738ba4505278c5c85e489e245fc51602890`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e923eb9ccd2d25e10956de8fd6fd7738ba4505278c5c85e489e245fc51602890`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e923eb9ccd2d25e10956de8fd6fd7738ba4505278c5c85e489e245fc51602890`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/mir/mir_span_thread_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_span_thread_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_span_thread_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_span_thread_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_span_thread_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/mir_span_thread_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives each hand-spanned HIR leaf its OWN span in the lowered MIR, and gives each compound Binary node ITS OWN span back rather than its last-lowered operand's' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
