# RISC-V Gen2 scalar-I RV32/RV64 product-cycle traceability

> Exercises a bounded scalar-I product-cycle witness through the existing closed RV32/RV64 product surface. The witnesses cover RV32 LUI and SLTU, RV32 register-count masking, RV64 word-result sign extension, and rejection before artifact creation. Each positive witness reaches generated VHDL analysis, elaboration, and held-retirement simulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 scalar-I RV32/RV64 product-cycle traceability

Exercises a bounded scalar-I product-cycle witness through the existing closed RV32/RV64 product surface. The witnesses cover RV32 LUI and SLTU, RV32 register-count masking, RV64 word-result sign extension, and rejection before artifact creation. Each positive witness reaches generated VHDL analysis, elaboration, and held-retirement simulation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/riscv_gen2_hwir_foundation.md |
| Plan | doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md |
| Design | doc/05_design/riscv_gen2_hwir_foundation.md |
| Research | doc/01_research/local/riscv_gen2_hwir_foundation.md |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_scalar_i_product_cycle_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises a bounded scalar-I product-cycle witness through the existing closed
RV32/RV64 product surface. The witnesses cover RV32 LUI and SLTU, RV32
register-count masking, RV64 word-result sign extension, and rejection before
artifact creation. Each positive witness reaches generated VHDL analysis,
elaboration, and held-retirement simulation.

## Claim boundary

GHDL is an admission gate: an unavailable runner is a failing result, never a
skip or a substitute source-level claim. Passing execution remains
development-stage host evidence and is not self-hosted qualification or a
complete scalar-core claim.

## Preconditions

- A VHDL-2008-capable GHDL runner is available to `ghdl_available()`.
- The strict scalar product compiler and RV32/RV64 default LSU configurations
  are available from the source under test.

## Examples

- `LUI 0x123451B7` retires `0x12345000` to `x3` in RV32.
- RV32 `SLL` with register count 33 retires `2`, proving architectural masking.
- RV64 `SRAW` with count 1 retires `0xFFFFFFFFC0000000`, proving arithmetic
  sign fill followed by the one allowed 32-bit-to-XLEN sign extension.

## Execution model

The scenario invokes `compile_strict_riscv_scalar_product`, not a leaf ALU
oracle or a hand-written VHDL fixture. The generated product therefore crosses
the existing scalar provider, completion skid, arbitration, fault aggregation,
and sole retirement owner before the testbench observes its record.

Each cycle witness drives one input acceptance, waits for retirement, holds the
retirement record under backpressure for one clock, consumes it once, and
requires the product to remain fault-free. A result-only test would not prove
the required product/cycle surface and is deliberately insufficient here.

## Vector policy

The RV32 LUI vector uses an upper immediate that has nonzero high bits so its
exact retirement value is observable. The RV32 SLTU vector is a true unsigned
comparison boundary: zero is below one. The RV32 SLL vector uses a count of 33
to require the 5-bit architectural count mask rather than a host conversion.

The RV64 SRAW vector has a negative 32-bit word and a count of 1. It catches
arithmetic sign fill, the XLEN-independent word result, and the resulting
single sign extension from 32 bits to XLEN. It does not claim all scalar-I
opcodes or all arithmetic-shift counts.

## External runner policy

The runner is probed through `ghdl_available()` before every positive cycle
case. No `skip` branch exists. If GHDL is missing, the asserted availability
check fails and later simulation steps do not fabricate evidence. A host must
provide VHDL-2008 analysis, elaboration, and simulation to pass this scenario.

Generated artifact paths are deterministic `/tmp/scalar_i_*_product.vhd`
paths. They are transient diagnostic material. A retained provenance-bound
receipt is produced only by the separately admitted self-hosted qualification
process, not by this SSpec or its generated manual.

## Rejection policy

The custom-major opcode `0x0000000B` is not an admitted scalar-I row. Its
product compilation must fail at the product entry boundary; this scenario does
not treat source-flow ordering as a retained-artifact receipt. It checks that
an unsupported row is rejected rather than assumed harmless at the VHDL or
simulator layer.

## Operator sequence

1. Start the executable SSpec with the normal project runtime lane.
2. Confirm that the runner rejects a missing GHDL installation as a failure.
3. Inspect the captured execution, artifact, and log evidence for each witness.
4. On analyzer, elaboration, or simulation failure, preserve the `/tmp` VHDL
   artifact and inspect the GHDL diagnostic before changing compiler code.
5. On a result, hold, or consumption failure, correct the scalar-I/product
   implementation; do not weaken the fixed instruction or expected record.
6. Do not use a passing host execution to mark a qualification receipt or a
   complete-core claim.

## Nonclaims

This scenario does not prove processor fetch/decode, memory, control-flow,
exception, CSR, M extension, compressed extension, physical implementation,
or complete scalar-I ISA coverage. It does not quantify target timing, area,
power, formal proof, or simulator diversity. It also does not replace the
separate self-hosted provenance and receipt authority gates.

**Requirements:** doc/02_requirements/feature/riscv_gen2_hwir_foundation.md

**Plan:** doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md

**Design:** doc/05_design/riscv_gen2_hwir_foundation.md

**Research:** doc/01_research/local/riscv_gen2_hwir_foundation.md

## Scenarios

### RISC-V Gen2 scalar-I RV32/RV64 product-cycle traceability

#### should retire RV32 upper-immediate and unsigned-comparison rows through the closed product

- Require the external GHDL VHDL-2008 cycle runner
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: ghdl_available() is true
- Build and run the RV32 LUI upper-immediate product-cycle witness
   - Log capture: after_step
- Confirm the RV32 product is monomorphic with no runtime opcode, extension, or XLEN selector
   - Log capture: after_step
- Build and run the RV32 SLTU unsigned-comparison product-cycle witness
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the external GHDL VHDL-2008 cycle runner")
expect(ghdl_available()).to_equal(true)
if not ghdl_available(): return
step("Build and run the RV32 LUI upper-immediate product-cycle witness")
step("Confirm the RV32 product is monomorphic with no runtime opcode, extension, or XLEN selector")
expect(scalar_i_product_has_no_runtime_selector("scalar_i_lui_rv32_shape",
    CoreConfig.rv32(), 0x123451B7)).to_equal(true)
expect(run_scalar_i_product_cycle("scalar_i_lui_rv32_product",
    "scalar_i_lui_rv32_product_tb", CoreConfig.rv32(), 0x123451B7,
    "00000000", "00000000", "12345000", "00011")).to_equal(true)
step("Build and run the RV32 SLTU unsigned-comparison product-cycle witness")
expect(run_scalar_i_product_cycle("scalar_i_sltu_rv32_product",
    "scalar_i_sltu_rv32_product_tb", CoreConfig.rv32(), 0x0020B1B3,
    "00000000", "00000001", "00000001", "00011")).to_equal(true)
```

</details>

#### should mask RV32 register shifts and sign-extend RV64 word arithmetic results exactly once

- Require the external GHDL VHDL-2008 cycle runner
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: ghdl_available() is true
- Build and run the RV32 SLL register-count masking witness
   - Log capture: after_step
- Build and run the RV64 SRAW word-result sign-extension witness
   - Log capture: after_step
- Confirm the RV64 product is monomorphic with no runtime opcode, extension, or XLEN selector
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the external GHDL VHDL-2008 cycle runner")
expect(ghdl_available()).to_equal(true)
if not ghdl_available(): return
step("Build and run the RV32 SLL register-count masking witness")
expect(run_scalar_i_product_cycle("scalar_i_sll_mask_rv32_product",
    "scalar_i_sll_mask_rv32_product_tb", CoreConfig.rv32(), 0x002091B3,
    "00000001", "00000021", "00000002", "00011")).to_equal(true)
step("Build and run the RV64 SRAW word-result sign-extension witness")
step("Confirm the RV64 product is monomorphic with no runtime opcode, extension, or XLEN selector")
expect(scalar_i_product_has_no_runtime_selector("scalar_i_sraw_rv64_shape",
    CoreConfig.rv64(), 0x4020D1BB)).to_equal(true)
expect(run_scalar_i_product_cycle("scalar_i_sraw_rv64_product",
    "scalar_i_sraw_rv64_product_tb", CoreConfig.rv64(), 0x4020D1BB,
    "0000000080000000", "0000000000000001", "FFFFFFFFC0000000",
    "00011")).to_equal(true)
```

</details>

#### should reject an unadmitted scalar-I instruction through the product entry boundary

- Require the external GHDL VHDL-2008 cycle runner
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: ghdl_available() is true
- Attempt to build an unadmitted custom major opcode through the scalar-I product surface
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: rejected.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the external GHDL VHDL-2008 cycle runner")
expect(ghdl_available()).to_equal(true)
if not ghdl_available(): return
step("Attempt to build an unadmitted custom major opcode through the scalar-I product surface")
val rejected = compile_strict_riscv_scalar_product("scalar_i_unadmitted",
    CoreConfig.rv32(), 0x0000000B, LsuConfig.rv32_product_default())
expect(rejected.is_success()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- **Plan:** `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- **Design:** `doc/05_design/riscv_gen2_hwir_foundation.md`
- **Research:** `doc/01_research/local/riscv_gen2_hwir_foundation.md`


</details>
