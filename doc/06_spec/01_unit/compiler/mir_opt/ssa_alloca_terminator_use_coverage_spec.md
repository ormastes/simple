# Ssa Alloca Terminator Use Coverage Specification

> Tests covering alloca lane terminator-operand coverage (bug class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssa Alloca Terminator Use Coverage Specification

## Scenarios

### alloca lane terminator-operand coverage (bug class)

#### collects the operand of every operand-carrying terminator as a use

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects the operand of every operand-carrying terminator as a use


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects the operand of every operand-carrying terminator as a use")
# The pure use-collection property, independent of the full transform.
# `Ret` returned an empty set here, which is the seed of the whole class.
val ret_uses = ssa_collect_term_operand_locals([], MirTerminator.Ret(Some(copy_operand(5))))
assert_contains(ret_uses, 5)
val if_uses = ssa_collect_term_operand_locals(
    [], MirTerminator.If(copy_operand(5), BlockId.new(2), BlockId.new(3))
)
assert_contains(if_uses, 5)
val switch_uses = ssa_collect_term_operand_locals(
    [], MirTerminator.Switch(copy_operand(5), [], BlockId.new(2))
)
assert_contains(switch_uses, 5)
```

</details>

#### treats an operand-free terminator as contributing no use

- treats an operand-free terminator as contributing no use


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an operand-free terminator as contributing no use")
# Guards the fix against over-correction: Ret(nil) must stay a no-op,
# otherwise a bogus local id enters the slot set.
val uses = ssa_collect_term_operand_locals([], MirTerminator.Ret(nil))
assert_equal(uses.len(), 0)
```

</details>

#### validates a returned operand rather than waving it through

- validates a returned operand rather than waving it through


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a returned operand rather than waving it through")
# `case Ret(_): true` admitted an undecodable payload unconditionally.
assert_true(ssa_term_operand_payloads_valid(MirTerminator.Ret(nil)))
assert_true(ssa_term_operand_payloads_valid(MirTerminator.Ret(Some(copy_operand(5)))))
```

</details>

#### slots and loads a local used only by a Ret terminator

- slots and loads a local used only by a Ret terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slots and loads a local used only by a Ret terminator")
val result = transform_with_tail_terminator(MirTerminator.Ret(Some(copy_operand(5))), [])
assert_true(result.applied)
assert_true(has_load(result.blocks[1]))
```

</details>

#### slots and loads a local used only by an If terminator

- slots and loads a local used only by an If terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slots and loads a local used only by an If terminator")
val result = transform_with_tail_terminator(
    MirTerminator.If(copy_operand(5), BlockId.new(2), BlockId.new(3)),
    [plain_block(2), plain_block(3)]
)
assert_true(result.applied)
assert_true(has_load(result.blocks[1]))
```

</details>

#### slots and loads a local used only by a Switch terminator

- slots and loads a local used only by a Switch terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slots and loads a local used only by a Switch terminator")
val result = transform_with_tail_terminator(
    MirTerminator.Switch(copy_operand(5), [], BlockId.new(2)),
    [plain_block(2)]
)
assert_true(result.applied)
assert_true(has_load(result.blocks[1]))
```

</details>

#### never leaves a slotted local read directly by the terminator

- never leaves a slotted local read directly by the terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never leaves a slotted local read directly by the terminator")
# The invariant that actually matters at llc: after slotting, no
# terminator may still name the original local -- it must name the
# loaded temporary. This is the assertion that fails if a future
# terminator kind is wired into liveness but not into the rewrite.
val result = transform_with_tail_terminator(MirTerminator.Ret(Some(copy_operand(5))), [])
assert_true(result.applied)
val direct_uses = ssa_collect_term_operand_locals([], result.blocks[1].terminator)
assert_false(direct_uses.contains(5))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering alloca lane terminator-operand coverage (bug class).
- alloca lane terminator-operand coverage (bug class)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `a8e3fa8943fab1609daa7dab635c0bab1b371ae040cbba4beb08d47e0e3ae777`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8e3fa8943fab1609daa7dab635c0bab1b371ae040cbba4beb08d47e0e3ae777`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8e3fa8943fab1609daa7dab635c0bab1b371ae040cbba4beb08d47e0e3ae777`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects the operand of every operand-carrying terminator as a use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats an operand-free terminator as contributing no use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates a returned operand rather than waving it through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
