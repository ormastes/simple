# hwir_zca_rv64_rows_spec

> Exercise source-level typed-HWIR construction for five bounded RV64 Zca rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_rv64_rows_spec

Exercise source-level typed-HWIR construction for five bounded RV64 Zca rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise source-level typed-HWIR construction for five bounded RV64 Zca rows.

The checks inspect classifiers, selected-width structure, configuration
rejection, and normalized effects. They do not execute emitted RTL or qualify
a processor, full Zca implementation, or architectural retirement behavior.

## Scenarios

### mission-critical RV64 Zca typed rows

#### should build both RV64-only OP-32 rows with explicit classifiers

- should build both RV64-only OP-32 rows with explicit classifiers
- Elaborate the bounded RV64 C.ADDW and C.SUBW rows
   - Expected: row.shape_diagnostic() equals ``
   - Expected: has_compare(row, classifiers[index]) is true
   - Expected: has_select_condition(row, classifiers[index]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should build both RV64-only OP-32 rows with explicit classifiers")
step("Elaborate the bounded RV64 C.ADDW and C.SUBW rows")
val config = CoreConfig.rv64_zca_mission_critical()
val rows = [strict_zca_caddw_rv64_row_hwir("rv64_caddw", config).ok().unwrap(),
    strict_zca_csubw_rv64_row_hwir("rv64_csubw", config).ok().unwrap()]
val classifiers = ["is_c_addw", "is_c_subw"]
var index = 0
for row in rows:
    expect(row.shape_diagnostic()).to_equal("")
    expect(has_compare(row, classifiers[index])).to_equal(true)
    expect(has_select_condition(row, classifiers[index])).to_equal(true)
    index = index + 1
```

</details>

#### should reject every RV64-only row for the RV32 critical product

- should reject every RV64-only row for the RV32 critical product
- Attempt to elaborate the RV64-only OP-32 rows under the RV32 profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject every RV64-only row for the RV32 critical product")
step("Attempt to elaborate the RV64-only OP-32 rows under the RV32 profile")
val config = CoreConfig.rv32_zca_mission_critical()
expect(strict_zca_caddw_rv64_row_hwir("rv32_caddw", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64")
expect(strict_zca_csubw_rv64_row_hwir("rv32_csubw", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64")
```

</details>

#### should use bit12 as shamt bit five in all RV64 six-bit shift rows

- should use bit12 as shamt bit five in all RV64 six-bit shift rows
- Elaborate each RV64 six-bit shift row and inspect the high shift-bit structure
   - Expected: row.shape_diagnostic() equals ``
   - Expected: row.summary.signal_count equals `row.signals.len()`
   - Expected: has_signal(row, "shamt_high") is true
   - Expected: has_compare(row, classifiers[index]) is true
   - Expected: strict_zca_slli6_rv64_row_hwir("rv32_slli6", CoreConfig.rv32_zca_mission_critical()).is_err() is true
   - Expected: strict_zca_srli6_rv64_row_hwir("rv32_srli6", CoreConfig.rv32_zca_mission_critical()).is_err() is true
   - Expected: strict_zca_srai6_rv64_row_hwir("rv32_srai6", CoreConfig.rv32_zca_mission_critical()).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should use bit12 as shamt bit five in all RV64 six-bit shift rows")
step("Elaborate each RV64 six-bit shift row and inspect the high shift-bit structure")
val config = CoreConfig.rv64_zca_mission_critical()
val slli = strict_zca_slli6_rv64_row_hwir("rv64_slli6", config)
if slli.is_err(): expect(slli.err().unwrap()).to_equal("")
val srli = strict_zca_srli6_rv64_row_hwir("rv64_srli6", config)
if srli.is_err(): expect(srli.err().unwrap()).to_equal("")
val srai = strict_zca_srai6_rv64_row_hwir("rv64_srai6", config)
if srai.is_err(): expect(srai.err().unwrap()).to_equal("")
val rows = [slli.ok().unwrap(), srli.ok().unwrap(), srai.ok().unwrap()]
val classifiers = ["is_c_slli6", "is_c_srli6", "is_c_srai6"]
var index = 0
for row in rows:
    expect(row.shape_diagnostic()).to_equal("")
    expect(row.summary.signal_count).to_equal(row.signals.len())
    expect(row.summary.comb_op_count).to_equal(
        row.comb_ops.len() + row.compare_ops.len() + row.select_ops.len())
    expect(has_signal(row, "shamt_high")).to_equal(true)
    expect(has_compare(row, classifiers[index])).to_equal(true)
    index = index + 1
expect(strict_zca_slli6_rv64_row_hwir("rv32_slli6", CoreConfig.rv32_zca_mission_critical()).is_err()).to_equal(true)
expect(strict_zca_srli6_rv64_row_hwir("rv32_srli6", CoreConfig.rv32_zca_mission_critical()).is_err()).to_equal(true)
expect(strict_zca_srai6_rv64_row_hwir("rv32_srai6", CoreConfig.rv32_zca_mission_critical()).is_err()).to_equal(true)
```

</details>

#### should normalize legality and architectural effects without canonical sentinels

- should normalize legality and architectural effects without canonical sentinels
- Construct the bounded normalized outcomes and inspect their explicit signals
   - Expected: outcome.shape_diagnostic() equals ``
   - Expected: has_signal(outcome, "match_legal") is true
   - Expected: has_signal(outcome, "effect_register_write") is true
   - Expected: has_signal(outcome, "effect_memory_read") is true
   - Expected: has_signal(outcome, "effect_memory_write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should normalize legality and architectural effects without canonical sentinels")
step("Construct the bounded normalized outcomes and inspect their explicit signals")
val config = CoreConfig.rv64_zca_mission_critical()
val outcomes = [strict_zca_caddw_rv64_outcome_hwir("out_caddw", config).ok().unwrap(),
    strict_zca_csubw_rv64_outcome_hwir("out_csubw", config).ok().unwrap(),
    strict_zca_slli6_rv64_outcome_hwir("out_slli6", config).ok().unwrap(),
    strict_zca_srli6_rv64_outcome_hwir("out_srli6", config).ok().unwrap(),
    strict_zca_srai6_rv64_outcome_hwir("out_srai6", config).ok().unwrap()]
for outcome in outcomes:
    expect(outcome.shape_diagnostic()).to_equal("")
    expect(has_signal(outcome, "match_legal")).to_equal(true)
    expect(has_signal(outcome, "effect_register_write")).to_equal(true)
    expect(has_signal(outcome, "effect_memory_read")).to_equal(true)
    expect(has_signal(outcome, "effect_memory_write")).to_equal(true)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1143aaec40c83527c9c3a47bc225041d54fc2cca4f195da681061c69ff3b3aa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1143aaec40c83527c9c3a47bc225041d54fc2cca4f195da681061c69ff3b3aa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1143aaec40c83527c9c3a47bc225041d54fc2cca4f195da681061c69ff3b3aa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build both RV64-only OP-32 rows with explicit classifiers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build both RV64-only OP-32 rows with explicit classifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every RV64-only row for the RV32 critical product' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject every RV64-only row for the RV32 critical product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use bit12 as shamt bit five in all RV64 six-bit shift rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use bit12 as shamt bit five in all RV64 six-bit shift rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize legality and architectural effects without canonical sentinels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
