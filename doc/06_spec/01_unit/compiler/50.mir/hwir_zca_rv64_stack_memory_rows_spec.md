# hwir_zca_rv64_stack_memory_rows_spec

> Exercise source-level typed-HWIR construction for bounded RV64 stack-memory rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_rv64_stack_memory_rows_spec

Exercise source-level typed-HWIR construction for bounded RV64 stack-memory rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise source-level typed-HWIR construction for bounded RV64 stack-memory rows.

The checks inspect row structure, fixed conversion vectors, RV32 rejection, and
explicit normalized effects. They do not run emitted RTL or qualify a processor,
stack-memory implementation, or complete compressed ISA.

## Scenarios

### mission-critical RV64 stack-relative doubleword rows

#### should pin C.LDSP 0x6522 to LD x10,8(x2) 0x00813503

- should pin C.LDSP 0x6522 to LD x10,8(x2) 0x00813503
- Elaborate the bounded RV64 C.LDSP row and inspect its typed conversion structure
   - Expected: row.shape_diagnostic() equals ``
   - Expected: has_comb(row, "shl", "imm_8_6", "imm_8_6_raw", "shl6") is true
   - Expected: has_comb(row, "shl", "imm_5", "imm_5_raw", "shl5") is true
   - Expected: has_comb(row, "shl", "imm_4_3", "imm_4_3_raw", "shl3") is true
   - Expected: has_compare(row, "rd_is_zero") is true
   - Expected: has_select(row, "legal_instruction", "rd_is_zero", "zero", "ld_instruction") is true
   - Expected: 25890 equals `0x6522`
   - Expected: 8467715 equals `0x00813503`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin C.LDSP 0x6522 to LD x10,8(x2) 0x00813503")
step("Elaborate the bounded RV64 C.LDSP row and inspect its typed conversion structure")
val row = strict_zca_ldsp_rv64_row_hwir("rv64_ldsp", CoreConfig.rv64_zca_mission_critical()).ok().unwrap()
expect(row.shape_diagnostic()).to_equal("")
expect(has_comb(row, "shl", "imm_8_6", "imm_8_6_raw", "shl6")).to_equal(true)
expect(has_comb(row, "shl", "imm_5", "imm_5_raw", "shl5")).to_equal(true)
expect(has_comb(row, "shl", "imm_4_3", "imm_4_3_raw", "shl3")).to_equal(true)
expect(has_compare(row, "rd_is_zero")).to_equal(true)
expect(has_select(row, "legal_instruction", "rd_is_zero", "zero", "ld_instruction")).to_equal(true)
expect(25890).to_equal(0x6522)
expect(8467715).to_equal(0x00813503)
```

</details>

#### should pin C.SDSP 0xe42a to SD x10,8(x2) 0x00a13423

- should pin C.SDSP 0xe42a to SD x10,8(x2) 0x00a13423
- Elaborate the bounded RV64 C.SDSP row and inspect its typed conversion structure
   - Expected: row.shape_diagnostic() equals ``
   - Expected: has_comb(row, "shl", "imm_8_6", "imm_8_6_raw", "shl6") is true
   - Expected: has_comb(row, "shl", "imm_5_3", "imm_5_3_raw", "shl3") is true
   - Expected: has_select(row, "canonical_instruction", "is_c_sdsp", "sd_instruction", "zero") is true
   - Expected: 58410 equals `0xe42a`
   - Expected: 10564643 equals `0x00a13423`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin C.SDSP 0xe42a to SD x10,8(x2) 0x00a13423")
step("Elaborate the bounded RV64 C.SDSP row and inspect its typed conversion structure")
val row = strict_zca_sdsp_rv64_row_hwir("rv64_sdsp", CoreConfig.rv64_zca_mission_critical()).ok().unwrap()
expect(row.shape_diagnostic()).to_equal("")
expect(has_comb(row, "shl", "imm_8_6", "imm_8_6_raw", "shl6")).to_equal(true)
expect(has_comb(row, "shl", "imm_5_3", "imm_5_3_raw", "shl3")).to_equal(true)
expect(has_select(row, "canonical_instruction", "is_c_sdsp", "sd_instruction", "zero")).to_equal(true)
expect(58410).to_equal(0xe42a)
expect(10564643).to_equal(0x00a13423)
```

</details>

#### should reject both RV64-only encodings during RV32 elaboration

- should reject both RV64-only encodings during RV32 elaboration
- Attempt to elaborate the RV64-only stack rows under the incompatible RV32 profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject both RV64-only encodings during RV32 elaboration")
step("Attempt to elaborate the RV64-only stack rows under the incompatible RV32 profile")
val config = CoreConfig.rv32_zca_mission_critical()
expect(strict_zca_ldsp_rv64_row_hwir("rv32_ldsp", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64")
expect(strict_zca_sdsp_rv64_row_hwir("rv32_sdsp", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64")
```

</details>

#### should gate every architectural effect with explicit match_legal

- should gate every architectural effect with explicit match_legal
- Construct normalized stack-row outcomes and inspect their legality gates
   - Expected: load.shape_diagnostic() equals ``
   - Expected: store.shape_diagnostic() equals ``
   - Expected: has_comb(load, "and", "effect_register_write", "match_legal", "read_value") is true
   - Expected: has_comb(load, "and", "effect_memory_read", "match_legal", "read_value") is true
   - Expected: has_comb(load, "and", "effect_memory_write", "match_legal", "write_value") is true
   - Expected: has_select(load, "legal_nonreserved", "ldsp64_rd_is_zero", "zero_flag", "one_flag") is true
   - Expected: has_comb(store, "and", "effect_register_write", "match_legal", "read_value") is true
   - Expected: has_comb(store, "and", "effect_memory_read", "match_legal", "read_value") is true
   - Expected: has_comb(store, "and", "effect_memory_write", "match_legal", "write_value") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should gate every architectural effect with explicit match_legal")
step("Construct normalized stack-row outcomes and inspect their legality gates")
val config = CoreConfig.rv64_zca_mission_critical()
val load = strict_zca_ldsp_rv64_outcome_hwir("rv64_ldsp_out", config).ok().unwrap()
val store = strict_zca_sdsp_rv64_outcome_hwir("rv64_sdsp_out", config).ok().unwrap()
expect(load.shape_diagnostic()).to_equal("")
expect(store.shape_diagnostic()).to_equal("")
expect(has_comb(load, "and", "effect_register_write", "match_legal", "read_value")).to_equal(true)
expect(has_comb(load, "and", "effect_memory_read", "match_legal", "read_value")).to_equal(true)
expect(has_comb(load, "and", "effect_memory_write", "match_legal", "write_value")).to_equal(true)
expect(has_select(load, "legal_nonreserved", "ldsp64_rd_is_zero", "zero_flag", "one_flag")).to_equal(true)
expect(has_comb(store, "and", "effect_register_write", "match_legal", "read_value")).to_equal(true)
expect(has_comb(store, "and", "effect_memory_read", "match_legal", "read_value")).to_equal(true)
expect(has_comb(store, "and", "effect_memory_write", "match_legal", "write_value")).to_equal(true)
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

- Canonical SPipe generation for source `5d9895a30148b595c87330d0926302e3a8df3ab46c2eec42441b5680dd56f17b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d9895a30148b595c87330d0926302e3a8df3ab46c2eec42441b5680dd56f17b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d9895a30148b595c87330d0926302e3a8df3ab46c2eec42441b5680dd56f17b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin C.LDSP 0x6522 to LD x10,8(x2) 0x00813503' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin C.LDSP 0x6522 to LD x10,8(x2) 0x00813503' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin C.SDSP 0xe42a to SD x10,8(x2) 0x00a13423' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin C.SDSP 0xe42a to SD x10,8(x2) 0x00a13423' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject both RV64-only encodings during RV32 elaboration' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject both RV64-only encodings during RV32 elaboration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate every architectural effect with explicit match_legal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
