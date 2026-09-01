# iso_use_after_move_e2e_spec

> End-to-end `iso` use-after-move — real SOURCE TEXT through the full pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# iso_use_after_move_e2e_spec

End-to-end `iso` use-after-move — real SOURCE TEXT through the full pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

End-to-end `iso` use-after-move — real SOURCE TEXT through the full pipeline.

Prior specs each proved one link of the chain in isolation:
- `borrow_check_spec.spl` hand-builds MIR and proves `BorrowChecker.check_function`
  detects use-after-move.
- `iso_move_pipeline_spec.spl` hand-builds HIR and proves MIR lowering emits a
  `Move` for an iso place-read let-binding (and documents, in its own header,
  that driving *source text* through `parse_full_frontend` for `iso` on a
  PARAMETER type used to be blocked by a parser gap, filed as
  doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md).
- `iso_parse_pipeline_spec.spl` proves `iso T` parses.

That parser gap has since been closed (src/compiler/10.frontend/core/parser.spl
"LANE ISO2" `iso` handling in `parser_parse_type_impl`, which is the same
generic type-position parser used for `val x: iso i64` local-variable
annotations, not just parameters). This spec is the missing keystone: it
drives real source text through
`parse_full_frontend -> HirLowering -> MirLowering -> check_mir_module`
and asserts on the real `BorrowChecker` result, with no hand-built HIR/MIR
anywhere.

The primary shape (cases 1-3) is a variable-to-variable let-binding
place-read of an iso source, followed by a second place-read of the same
now-moved source, matching `iso_move_pipeline_spec.spl`'s proven hand-built
shape. `iso_move_pipeline_spec.spl`'s own comments additionally claim a bare
trailing use in a call argument / return position is a SEPARATE, known
blind spot in the checker's terminator conversion. Case 4 below measures
that claim directly, with real source text, rather than taking it on faith
-- see its result for what this pipeline actually does with `print x` after
a move.

## Scenarios

### iso use-after-move, real source text through the full pipeline

#### reports a use-after-move error for a moved-then-reused iso local

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a use-after-move error for a moved-then-reused iso local


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a use-after-move error for a moved-then-reused iso local")
val errors = errors_for_source(iso_move_then_use_source(), "iso_use_after_move")
assert_true(errors.len() > 0)
```

</details>

#### reports no error for the same shape when the moved source is never reused

- reports no error for the same shape when the moved source is never reused


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no error for the same shape when the moved source is never reused")
val errors = errors_for_source(iso_move_no_reuse_source(), "iso_move_no_reuse")
assert_true(errors.len() == 0)
```

</details>

#### reports no error for the identical shape without `iso` (non-iso control)

- reports no error for the identical shape without `iso` (non-iso control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no error for the identical shape without `iso` (non-iso control)")
val errors = errors_for_source(non_iso_same_shape_source(), "non_iso_control")
assert_true(errors.len() == 0)
```

</details>

#### reports a use-after-move error for a moved iso local used as a call argument (`print x`)

- reports a use-after-move error for a moved iso local used as a call argument (`print x`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a use-after-move error for a moved iso local used as a call argument (`print x`)")
# This is the literal shape named by the task this spec was written
# for. It is a SEPARATE oracle from case 1: case 1 already proves the
# move is emitted and detected for a let-binding reuse: if THIS case
# is red while case 1 is green, the break is localized to
# call-argument use-detection, not move-emission.
val errors = errors_for_source(iso_move_then_print_source(), "iso_use_after_move_call_arg")
assert_true(errors.len() > 0)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b545006a10d565d189657990b1f6f9f58f316a88022947ea4f600e18abf7052`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b545006a10d565d189657990b1f6f9f58f316a88022947ea4f600e18abf7052`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b545006a10d565d189657990b1f6f9f58f316a88022947ea4f600e18abf7052`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl
mirror: doc/06_spec/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a use-after-move error for a moved-then-reused iso local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no error for the same shape when the moved source is never reused' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no error for the identical shape without `iso` (non-iso control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
