# hwir_migrating_overlap_guard_spec

> Exercise the source-level overlap guard for the bounded migrating Zca composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_migrating_overlap_guard_spec

Exercise the source-level overlap guard for the bounded migrating Zca composition.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise the source-level overlap guard for the bounded migrating Zca composition.

The scenario inspects typed driver ownership and deterministic emitter text. It
does not run generated VHDL/RTL, prove a complete decoder, or qualify a
processor or architectural retirement path.

## Scenarios

### critical migrating Zca overlap guard

#### should fail closed instead of letting priority select an ambiguous row

- should fail closed instead of letting priority select an ambiguous row
- Build the bounded migrating composition and inspect its unique-driver overlap gate
   - Expected: module.shape_diagnostic() equals ``
   - Expected: overlap_guard_driver_count(module, "canonical_instruction") equals `1`
   - Expected: overlap_guard_driver_count(module, "legal") equals `1`
   - Expected: overlap_guard_driver_count(module, "next_pc") equals `1`
   - Expected: overlap_guard_driver_count(module, "redirect_valid") equals `1`
   - Expected: overlap_guard_driver_count(module, "redirect_target") equals `1`
   - Expected: no_overlap_gate is true
   - Expected: unique_legal_gate is true
   - Expected: rendered.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed instead of letting priority select an ambiguous row")
step("Build the bounded migrating composition and inspect its unique-driver overlap gate")
val module = strict_zca_migrating_predecode_hwir("critical_overlap_guard",
    CoreConfig.rv32_zca_mission_critical()).unwrap()
expect(module.shape_diagnostic()).to_equal("")
expect(overlap_guard_driver_count(module, "canonical_instruction")).to_equal(1)
expect(overlap_guard_driver_count(module, "legal")).to_equal(1)
expect(overlap_guard_driver_count(module, "next_pc")).to_equal(1)
expect(overlap_guard_driver_count(module, "redirect_valid")).to_equal(1)
expect(overlap_guard_driver_count(module, "redirect_target")).to_equal(1)
var no_overlap_gate = false
var unique_legal_gate = false
for op in module.select_ops:
    if op.result == "migrating_no_overlap" and
        op.when_true == "migrating_zero_flag" and
        op.when_false == "migrating_one_flag":
        no_overlap_gate = true
    if op.result == "canonical_instruction" and
        op.condition == "migrating_no_overlap" and
        op.when_false == "migrating_zero_instruction":
        unique_legal_gate = true
expect(no_overlap_gate).to_equal(true)
expect(unique_legal_gate).to_equal(true)
val rendered = render_strict_hwir_vhdl(module)
expect(rendered.is_success()).to_equal(true)
expect(rendered.vhdl).to_contain("migrating_no_overlap <= migrating_zero_flag when")
expect(rendered.vhdl).to_contain("canonical_instruction <= migrating_canonical_after_0 when migrating_no_overlap = '1' else migrating_zero_instruction;")
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
- `REQ-G2-011`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `068a645181f09c19b3fa20c71e0b00eb33be5e93fa28eeee8436b49ad8a4b40e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `068a645181f09c19b3fa20c71e0b00eb33be5e93fa28eeee8436b49ad8a4b40e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `068a645181f09c19b3fa20c71e0b00eb33be5e93fa28eeee8436b49ad8a4b40e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed instead of letting priority select an ambiguous row' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed instead of letting priority select an ambiguous row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
