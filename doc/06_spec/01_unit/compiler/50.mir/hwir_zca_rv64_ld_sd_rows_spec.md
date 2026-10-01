# hwir_zca_rv64_ld_sd_rows_spec

> Exercise source-level typed-HWIR construction for the bounded RV64 C.LD/C.SD rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_rv64_ld_sd_rows_spec

Exercise source-level typed-HWIR construction for the bounded RV64 C.LD/C.SD rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise source-level typed-HWIR construction for the bounded RV64 C.LD/C.SD rows.

The checks inspect row shape, fixed conversion vectors, configuration rejection,
and explicit normalized effects. They do not run emitted RTL or qualify a
processor, memory subsystem, or complete compressed ISA.

## Scenarios

### mission-critical RV64 C.LD and C.SD rows

#### should pin C.LD vector 0x6480 to canonical LD x8,8(x9) 0x0084b403

- should pin C.LD vector 0x6480 to canonical LD x8,8(x9) 0x0084b403
- Elaborate the bounded RV64 C.LD row and inspect its typed conversion structure
   - Expected: row.shape_diagnostic() equals ``
   - Expected: constant_value(row, "opcode_tag_mask") equals `57347`
   - Expected: constant_value(row, "expected_tag") equals `24576`
   - Expected: constant_value(row, "dword_funct3") equals `12288`
   - Expected: constant_value(row, "base_opcode") equals `3`
   - Expected: has_comb(row, "shl", "imm_7_6", "imm_7_6_compact", "left_shift_6") is true
   - Expected: has_comb(row, "shl", "imm_5_3", "imm_5_3_compact", "left_shift_3") is true
   - Expected: has_select(row, "canonical_instruction", "is_c_ld", "ld_instruction") is true
   - Expected: cld_reference(25728) equals `8696835`
   - Expected: cld_reference(24576) equals `275459`
   - Expected: cld_reference(32764) equals `260552579`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin C.LD vector 0x6480 to canonical LD x8,8(x9) 0x0084b403")
step("Elaborate the bounded RV64 C.LD row and inspect its typed conversion structure")
val row = strict_zca_cld_rv64_row_hwir("rv64_cld", CoreConfig.rv64_zca_mission_critical()).ok().unwrap()
expect(row.shape_diagnostic()).to_equal("")
expect(constant_value(row, "opcode_tag_mask")).to_equal(57347)
expect(constant_value(row, "expected_tag")).to_equal(24576)
expect(constant_value(row, "dword_funct3")).to_equal(12288)
expect(constant_value(row, "base_opcode")).to_equal(3)
expect(has_comb(row, "shl", "imm_7_6", "imm_7_6_compact", "left_shift_6")).to_equal(true)
expect(has_comb(row, "shl", "imm_5_3", "imm_5_3_compact", "left_shift_3")).to_equal(true)
expect(has_select(row, "canonical_instruction", "is_c_ld", "ld_instruction")).to_equal(true)
expect(cld_reference(25728)).to_equal(8696835)
expect(cld_reference(24576)).to_equal(275459)
expect(cld_reference(32764)).to_equal(260552579)
```

</details>

#### should pin C.SD vector 0xe880 to canonical SD x8,16(x9) 0x0084b823

- should pin C.SD vector 0xe880 to canonical SD x8,16(x9) 0x0084b823
- Elaborate the bounded RV64 C.SD row and inspect its typed conversion structure
   - Expected: row.shape_diagnostic() equals ``
   - Expected: constant_value(row, "opcode_tag_mask") equals `57347`
   - Expected: constant_value(row, "expected_tag") equals `57344`
   - Expected: constant_value(row, "dword_funct3") equals `12288`
   - Expected: constant_value(row, "base_opcode") equals `35`
   - Expected: has_comb(row, "shl", "imm_upper_field", "immediate_shifted_5", "left_shift_25") is true
   - Expected: has_comb(row, "shl", "imm_low_field", "imm_low_bits", "left_shift_7") is true
   - Expected: has_select(row, "canonical_instruction", "is_c_sd", "sd_instruction") is true
   - Expected: csd_reference(59520) equals `8697891`
   - Expected: csd_reference(57344) equals `8663075`
   - Expected: csd_reference(65532) equals `251116579`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin C.SD vector 0xe880 to canonical SD x8,16(x9) 0x0084b823")
step("Elaborate the bounded RV64 C.SD row and inspect its typed conversion structure")
val row = strict_zca_csd_rv64_row_hwir("rv64_csd", CoreConfig.rv64_zca_mission_critical()).ok().unwrap()
expect(row.shape_diagnostic()).to_equal("")
expect(constant_value(row, "opcode_tag_mask")).to_equal(57347)
expect(constant_value(row, "expected_tag")).to_equal(57344)
expect(constant_value(row, "dword_funct3")).to_equal(12288)
expect(constant_value(row, "base_opcode")).to_equal(35)
expect(has_comb(row, "shl", "imm_upper_field", "immediate_shifted_5", "left_shift_25")).to_equal(true)
expect(has_comb(row, "shl", "imm_low_field", "imm_low_bits", "left_shift_7")).to_equal(true)
expect(has_select(row, "canonical_instruction", "is_c_sd", "sd_instruction")).to_equal(true)
expect(csd_reference(59520)).to_equal(8697891)
expect(csd_reference(57344)).to_equal(8663075)
expect(csd_reference(65532)).to_equal(251116579)
```

</details>

#### should reject both rows during RV32 elaboration because encodings overlap Zcf

- should reject both rows during RV32 elaboration because encodings overlap Zcf
- Attempt to elaborate the RV64-only rows under the incompatible RV32 profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject both rows during RV32 elaboration because encodings overlap Zcf")
step("Attempt to elaborate the RV64-only rows under the incompatible RV32 profile")
val config = CoreConfig.rv32_zca_mission_critical()
expect(strict_zca_cld_rv64_row_hwir("rv32_cld", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64-MEMORY")
expect(strict_zca_csd_rv64_row_hwir("rv32_csd", config).err().unwrap()).to_contain("HWIR-E-ZCA-RV64-MEMORY")
```

</details>

#### should gate truthful architectural effects with explicit match_legal

- should gate truthful architectural effects with explicit match_legal
- Construct normalized C.LD and C.SD outcomes and inspect their legality gates
   - Expected: load.shape_diagnostic() equals ``
   - Expected: store.shape_diagnostic() equals ``
   - Expected: unary_source(load, "legal") equals `match_legal`
   - Expected: unary_source(load, "effect_register_write") equals `match_legal`
   - Expected: unary_source(load, "effect_memory_read") equals `match_legal`
   - Expected: unary_source(load, "effect_memory_write") equals `zero_flag`
   - Expected: unary_source(store, "effect_register_write") equals `zero_flag`
   - Expected: unary_source(store, "effect_memory_read") equals `zero_flag`
   - Expected: unary_source(store, "effect_memory_write") equals `match_legal`
   - Expected: has_select(load, "match_legal", "cld_is_c_ld", "one_flag") is true
   - Expected: has_select(store, "match_legal", "csd_is_c_sd", "one_flag") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should gate truthful architectural effects with explicit match_legal")
step("Construct normalized C.LD and C.SD outcomes and inspect their legality gates")
val config = CoreConfig.rv64_zca_mission_critical()
val load = strict_zca_cld_rv64_outcome_hwir("rv64_cld_outcome", config).ok().unwrap()
val store = strict_zca_csd_rv64_outcome_hwir("rv64_csd_outcome", config).ok().unwrap()
expect(load.shape_diagnostic()).to_equal("")
expect(store.shape_diagnostic()).to_equal("")
expect(unary_source(load, "legal")).to_equal("match_legal")
expect(unary_source(load, "effect_register_write")).to_equal("match_legal")
expect(unary_source(load, "effect_memory_read")).to_equal("match_legal")
expect(unary_source(load, "effect_memory_write")).to_equal("zero_flag")
expect(unary_source(store, "effect_register_write")).to_equal("zero_flag")
expect(unary_source(store, "effect_memory_read")).to_equal("zero_flag")
expect(unary_source(store, "effect_memory_write")).to_equal("match_legal")
expect(has_select(load, "match_legal", "cld_is_c_ld", "one_flag")).to_equal(true)
expect(has_select(store, "match_legal", "csd_is_c_sd", "one_flag")).to_equal(true)
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

- Canonical SPipe generation for source `61d94e76e3152113bbeeca12ee1b50ff59250f266cc8f143e56487749fdf7400`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61d94e76e3152113bbeeca12ee1b50ff59250f266cc8f143e56487749fdf7400`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61d94e76e3152113bbeeca12ee1b50ff59250f266cc8f143e56487749fdf7400`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin C.LD vector 0x6480 to canonical LD x8,8(x9) 0x0084b403' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin C.LD vector 0x6480 to canonical LD x8,8(x9) 0x0084b403' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin C.SD vector 0xe880 to canonical SD x8,16(x9) 0x0084b823' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin C.SD vector 0xe880 to canonical SD x8,16(x9) 0x0084b823' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject both rows during RV32 elaboration because encodings overlap Zcf' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject both rows during RV32 elaboration because encodings overlap Zcf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate truthful architectural effects with explicit match_legal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
