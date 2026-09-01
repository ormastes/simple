# hwir_zca_load_effect_outcomes_spec

> Exercise source-level normalized outcome metadata for bounded Zca load rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_load_effect_outcomes_spec

Exercise source-level normalized outcome metadata for bounded Zca load rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise source-level normalized outcome metadata for bounded Zca load rows.

The checks inspect explicit legality and architectural-effect signals only. They
do not issue memory transactions, execute emitted RTL, or qualify a processor
or complete compressed ISA implementation.

## Scenarios

### normalized Zca load effects

#### should gate both C.LW memory read and register writeback with tag legality

- should gate both C.LW memory read and register writeback with tag legality
- Construct the bounded C.LW outcome and inspect explicit effect gates
   - Expected: outcome.shape_diagnostic() equals ``
   - Expected: constant_value(outcome, "effect_register_write_value") equals `1`
   - Expected: constant_value(outcome, "effect_memory_read_value") equals `1`
   - Expected: constant_value(outcome, "effect_memory_write_value") equals `0`
   - Expected: has_gate(outcome, "effect_register_write", "effect_register_write_value") is true
   - Expected: has_gate(outcome, "effect_memory_read", "effect_memory_read_value") is true
   - Expected: has_gate(outcome, "effect_memory_write", "effect_memory_write_value") is true
   - Expected: has_select(outcome, "match_legal", "lw_is_c_lw", "one_flag", "zero_flag") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should gate both C.LW memory read and register writeback with tag legality")
step("Construct the bounded C.LW outcome and inspect explicit effect gates")
val outcome = strict_zca_lw_outcome_hwir("load_effect_lw", CoreConfig.rv32_zca_mission_critical()).ok().unwrap()
expect(outcome.shape_diagnostic()).to_equal("")
expect(constant_value(outcome, "effect_register_write_value")).to_equal(1)
expect(constant_value(outcome, "effect_memory_read_value")).to_equal(1)
expect(constant_value(outcome, "effect_memory_write_value")).to_equal(0)
expect(has_gate(outcome, "effect_register_write", "effect_register_write_value")).to_equal(true)
expect(has_gate(outcome, "effect_memory_read", "effect_memory_read_value")).to_equal(true)
expect(has_gate(outcome, "effect_memory_write", "effect_memory_write_value")).to_equal(true)
expect(has_select(outcome, "match_legal", "lw_is_c_lw", "one_flag", "zero_flag")).to_equal(true)
```

</details>

#### should suppress both C.LWSP effects when rd is zero or the tag does not match

- should suppress both C.LWSP effects when rd is zero or the tag does not match
- Construct the bounded C.LWSP outcome and inspect tag and reserved-register gates
   - Expected: outcome.shape_diagnostic() equals ``
   - Expected: constant_value(outcome, "effect_register_write_value") equals `1`
   - Expected: constant_value(outcome, "effect_memory_read_value") equals `1`
   - Expected: constant_value(outcome, "effect_memory_write_value") equals `0`
   - Expected: has_gate(outcome, "effect_register_write", "effect_register_write_value") is true
   - Expected: has_gate(outcome, "effect_memory_read", "effect_memory_read_value") is true
   - Expected: has_select(outcome, "lwsp_legal_after_reserved_0", "lwsp_rd_is_zero", "zero_flag", "one_flag") is true
   - Expected: has_select(outcome, "match_legal", "lwsp_is_c_lwsp", "lwsp_legal_after_reserved_0", "zero_flag") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should suppress both C.LWSP effects when rd is zero or the tag does not match")
step("Construct the bounded C.LWSP outcome and inspect tag and reserved-register gates")
val outcome = strict_zca_lwsp_outcome_hwir("load_effect_lwsp", CoreConfig.rv64_zca_mission_critical()).ok().unwrap()
expect(outcome.shape_diagnostic()).to_equal("")
expect(constant_value(outcome, "effect_register_write_value")).to_equal(1)
expect(constant_value(outcome, "effect_memory_read_value")).to_equal(1)
expect(constant_value(outcome, "effect_memory_write_value")).to_equal(0)
expect(has_gate(outcome, "effect_register_write", "effect_register_write_value")).to_equal(true)
expect(has_gate(outcome, "effect_memory_read", "effect_memory_read_value")).to_equal(true)
expect(has_select(outcome, "lwsp_legal_after_reserved_0", "lwsp_rd_is_zero", "zero_flag", "one_flag")).to_equal(true)
expect(has_select(outcome, "match_legal", "lwsp_is_c_lwsp", "lwsp_legal_after_reserved_0", "zero_flag")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a882a19cf03b2770423f1fec01b6f66d8eabde3d993c1763849b6ae4cd5b431a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a882a19cf03b2770423f1fec01b6f66d8eabde3d993c1763849b6ae4cd5b431a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a882a19cf03b2770423f1fec01b6f66d8eabde3d993c1763849b6ae4cd5b431a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate both C.LW memory read and register writeback with tag legality' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should gate both C.LW memory read and register writeback with tag legality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should suppress both C.LWSP effects when rd is zero or the tag does not match' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should suppress both C.LWSP effects when rd is zero or the tag does not match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
