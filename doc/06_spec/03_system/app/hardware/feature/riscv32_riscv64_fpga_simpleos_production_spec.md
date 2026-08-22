# RV32/RV64 Simple-Generated FPGA CPU and Linux

> Verifies the riscv32 riscv64 fpga simpleos production behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32/RV64 Simple-Generated FPGA CPU and Linux

Verifies the riscv32 riscv64 fpga simpleos production behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the riscv32 riscv64 fpga simpleos production behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### RV32/RV64 Simple-generated FPGA CPU and Linux production qualification

#### should qualify compiler-generated RV32 and RV64 through interactive Linux on KV260

- Verify: should qualify compiler-generated RV32 and RV64 through interactive Linux on KV260
   - Artifact capture: after_step
- Generate RV32 and RV64 RTL from Simple sources
   - Artifact capture: after_step
- Verify compiler provenance source maps deterministic hashes and semantic RVFI
   - Artifact capture: after_step
- Exercise Sv32 and Sv39 translation plus PMP protection
   - Artifact capture: after_step
- Verify translated protected fetch load store and precise faults for both XLENs
   - Artifact capture: after_step
- Boot Linux to an interactive login on generated RTL
   - Artifact capture: after_step
- Verify pinned media and separate generated-RTL login evidence
   - Artifact capture: after_step
- Run terminal login and list guest files
   - Artifact capture: after_step
- Verify bidirectional terminal commands prompts and root entries
   - Artifact capture: after_step
- Program each FPGA image and capture board-origin evidence
   - Artifact capture: after_step
- Verify independent RV32 and RV64 KV260 cold and warm boot evidence
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should qualify compiler-generated RV32 and RV64 through interactive Linux on KV260")
step("Generate RV32 and RV64 RTL from Simple sources")
generate_dual_arch_rtl_evidence()

step("Exercise Sv32 and Sv39 translation plus PMP protection")
require_dual_arch_mmu_pmp_evidence()

step("Boot Linux to an interactive login on generated RTL")
require_generated_rtl_linux_login_evidence()

step("Run terminal login and list guest files")
require_terminal_login_ls_evidence()

step("Program each FPGA image and capture board-origin evidence")
require_dual_arch_board_origin_evidence()
```

</details>

<details>
<summary>Advanced: should reject noncanonical generated RTL and false testbench success</summary>

#### should reject noncanonical generated RTL and false testbench success

- Verify: should reject noncanonical generated RTL and false testbench success
   - Log capture: after_step
- Substitute empty constant copied external fallback or emitted-string CPU RTL
   - Log capture: after_step
- Run compiler provenance and generated RTL validation
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject noncanonical generated RTL and false testbench success")
step("Substitute empty constant copied external fallback or emitted-string CPU RTL")
step("Run compiler provenance and generated RTL validation")
reject_noncanonical_rtl_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject bypassed protection and evidence reused across architectures</summary>

#### should reject bypassed protection and evidence reused across architectures

- Verify: should reject bypassed protection and evidence reused across architectures
   - Log capture: after_step
- Bypass Sv32 Sv39 or PMP before a memory bus request
   - Log capture: after_step
- Reuse an RV32 profile artifact or transcript for RV64 or vice versa
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject bypassed protection and evidence reused across architectures")
step("Bypass Sv32 Sv39 or PMP before a memory bus request")
step("Reuse an RV32 profile artifact or transcript for RV64 or vice versa")
reject_unprotected_or_cross_arch_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject QEMU output-only or synthesized Linux terminal evidence</summary>

#### should reject QEMU output-only or synthesized Linux terminal evidence

- Verify: should reject QEMU output-only or synthesized Linux terminal evidence
   - Log capture: after_step
- Submit QEMU media output or a TX-only marker as generated RTL or board proof
   - Log capture: after_step
- Remove UART input command evidence or alter pinned Linux artifact hashes
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject QEMU output-only or synthesized Linux terminal evidence")
step("Submit QEMU media output or a TX-only marker as generated RTL or board proof")
step("Remove UART input command evidence or alter pinned Linux artifact hashes")
reject_qemu_or_output_only_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject vacuous RVFI formal and inaccurate ACT4 evidence</summary>

#### should reject vacuous RVFI formal and inaccurate ACT4 evidence

- Verify: should reject vacuous RVFI formal and inaccurate ACT4 evidence
   - Artifact capture: after_step
- Hold RVFI constant remove formal assertions or disconnect the emitted DUT
   - Artifact capture: after_step
- Declare unsupported ISA privilege MMU or PMP behavior in the ACT4 profile
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject vacuous RVFI formal and inaccurate ACT4 evidence")
step("Hold RVFI constant remove formal assertions or disconnect the emitted DUT")
step("Declare unsupported ISA privilege MMU or PMP behavior in the ACT4 profile")
reject_vacuous_formal_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject stale mismatched or noninteractive physical FPGA evidence</summary>

#### should reject stale mismatched or noninteractive physical FPGA evidence

- Verify: should reject stale mismatched or noninteractive physical FPGA evidence
   - Protocol capture: after_step
- Program a stale wrong-architecture or timing-failing bitstream
   - Protocol capture: after_step
- Provide only ILA output or omit cold warm login and ls terminal interaction
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject stale mismatched or noninteractive physical FPGA evidence")
step("Program a stale wrong-architecture or timing-failing bitstream")
step("Provide only ILA output or omit cold warm login and ls terminal interaction")
reject_stale_physical_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject incomplete provenance stale manuals and unreviewed done marks</summary>

#### should reject incomplete provenance stale manuals and unreviewed done marks

- Verify: should reject incomplete provenance stale manuals and unreviewed done marks
   - Artifact capture: after_step
- Remove commands hashes requirement links generated manual content or review records
   - Artifact capture: after_step
- Run SPipe documentation and production-readiness audits
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject incomplete provenance stale manuals and unreviewed done marks")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Remove commands hashes requirement links generated manual content or review records")
step("Run SPipe documentation and production-readiness audits")
reject_incomplete_manual_or_provenance()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8927d49a6322e0f41877ef0b408376ba1def668c23e56c80dd9fc8360b3c086b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8927d49a6322e0f41877ef0b408376ba1def668c23e56c80dd9fc8360b3c086b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8927d49a6322e0f41877ef0b408376ba1def668c23e56c80dd9fc8360b3c086b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:179:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should qualify compiler-generated RV32 and RV64 through interactive Linux on KV260' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:205:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject noncanonical generated RTL and false testbench success' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject bypassed protection and evidence reused across architectures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:225:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject QEMU output-only or synthesized Linux terminal evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject vacuous RVFI formal and inaccurate ACT4 evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl:246:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject stale mismatched or noninteractive physical FPGA evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
