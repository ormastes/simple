# simple_riscv_hardening_ac5_spec

> Verifies the simple riscv hardening ac5 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_riscv_hardening_ac5_spec

Verifies the simple riscv hardening ac5 behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simple riscv hardening ac5 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Simple RISC-V hardening AC-5

#### should emit the production RV32 core without unreachable scratch RTL

- Verify: should emit the production RV32 core without unreachable scratch RTL
- Generate the production RV32 base core with debug taps enabled
- Confirm the generated artifact is the real RV32 core and retains its ROM owners
- Apply the fail-closed dead-scratch contract
   - Expected: rv32_dead_scratch_contract_error(generated) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should emit the production RV32 core without unreachable scratch RTL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the production RV32 base core with debug taps enabled")
val generated = generate_exec_core(XlenConfig.rv32(), "", true)
step("Confirm the generated artifact is the real RV32 core and retains its ROM owners")
expect(generated).to_start_with("library ieee;")
expect(generated).to_contain("architecture rtl of rv32_exec_core is")
expect(generated).to_contain("signal rom_a : rom_t := init_rom;")
expect(generated).to_contain("signal data_rom : data_rom_t := init_data_rom;")
step("Apply the fail-closed dead-scratch contract")
expect(rv32_dead_scratch_contract_error(generated)).to_equal("")
```

</details>

#### should keep the checked-in golden identical to production generation

- Verify: should keep the checked-in golden identical to production generation
- Generate the RV32 base core and load the pinned golden
- Reject a missing or stale golden before comparing bytes
   - Expected: rv32_dead_scratch_contract_error(golden) equals ``
- Compare the complete generated and checked-in artifacts
   - Expected: golden equals `generated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should keep the checked-in golden identical to production generation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the RV32 base core and load the pinned golden")
val generated = generate_exec_core(XlenConfig.rv32(), "", true)
val golden = file_read_text(RV32_GOLDEN_PATH)
step("Reject a missing or stale golden before comparing bytes")
expect(rv32_dead_scratch_contract_error(golden)).to_equal("")
expect(golden.len()).to_be_greater_than(0)
step("Compare the complete generated and checked-in artifacts")
expect(golden).to_equal(generated)
```

</details>

#### should remain scratch-free across the optional debug-tap edge

- Verify: should remain scratch-free across the optional debug-tap edge
- Generate the same RV32 core with debug taps disabled and enabled
- Confirm the aspect switch changes only the intended debug surface
   - Expected: without_debug does not contain `dbg_reg_addr`
   - Expected: with_debug contains `dbg_reg_addr`
- Apply the dead-scratch contract to both aspect products
   - Expected: rv32_dead_scratch_contract_error(without_debug) equals ``
   - Expected: rv32_dead_scratch_contract_error(with_debug) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should remain scratch-free across the optional debug-tap edge")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the same RV32 core with debug taps disabled and enabled")
val without_debug = generate_exec_core(XlenConfig.rv32(), "", false)
val with_debug = generate_exec_core(XlenConfig.rv32(), "", true)
step("Confirm the aspect switch changes only the intended debug surface")
expect(without_debug.contains("dbg_reg_addr")).to_equal(false)
expect(with_debug.contains("dbg_reg_addr")).to_equal(true)
step("Apply the dead-scratch contract to both aspect products")
expect(rv32_dead_scratch_contract_error(without_debug)).to_equal("")
expect(rv32_dead_scratch_contract_error(with_debug)).to_equal("")
```

</details>

#### should reject missing and historical scratch artifacts with stable errors

- Verify: should reject missing and historical scratch artifacts with stable errors
- Submit an empty artifact to calibrate missing-core rejection
   - Expected: rv32_dead_scratch_contract_error("") equals `RSH-AC5-E-NOT-RV32-CORE`
- Submit each historical stale-artifact class independently
   - Expected: rv32_dead_scratch_contract_error(core + "constant SCRATCH_BASE_WORD") equals `RSH-AC5-E-SCRATCH-GEOMETRY`
   - Expected: rv32_dead_scratch_contract_error(core + "signal scratch : scratch_t") equals `RSH-AC5-E-SCRATCH-STORAGE`
   - Expected: rv32_dead_scratch_contract_error(core + "signal stack_ra_ab5c_q") equals `RSH-AC5-E-PAYLOAD-REGISTER`
   - Expected: rv32_dead_scratch_contract_error(core + "x\"8002AB5C\"") equals `RSH-AC5-E-PAYLOAD-ADDRESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RISCV-HARDEN-005
step("Verify: should reject missing and historical scratch artifacts with stable errors")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Submit an empty artifact to calibrate missing-core rejection")
expect(rv32_dead_scratch_contract_error("")).to_equal("RSH-AC5-E-NOT-RV32-CORE")
val core = "architecture rtl of rv32_exec_core is\n"
step("Submit each historical stale-artifact class independently")
expect(rv32_dead_scratch_contract_error(core + "constant SCRATCH_BASE_WORD")).to_equal("RSH-AC5-E-SCRATCH-GEOMETRY")
expect(rv32_dead_scratch_contract_error(core + "signal scratch : scratch_t")).to_equal("RSH-AC5-E-SCRATCH-STORAGE")
expect(rv32_dead_scratch_contract_error(core + "signal stack_ra_ab5c_q")).to_equal("RSH-AC5-E-PAYLOAD-REGISTER")
expect(rv32_dead_scratch_contract_error(core + "x\"8002AB5C\"")).to_equal("RSH-AC5-E-PAYLOAD-ADDRESS")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f84fdaeb53dac76a2bbdebff98034adc8f8901a8071d7200c830a1200c709ff1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f84fdaeb53dac76a2bbdebff98034adc8f8901a8071d7200c830a1200c709ff1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f84fdaeb53dac76a2bbdebff98034adc8f8901a8071d7200c830a1200c709ff1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit the production RV32 core without unreachable scratch RTL' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the checked-in golden identical to production generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remain scratch-free across the optional debug-tap edge' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing and historical scratch artifacts with stable errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
