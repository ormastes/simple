# RISC-V Gen2 CSR product-cycle evidence

> Exercises a concrete RV32 Zicsr/Zifencei product through generated VHDL and a clocked CSR access/commit/retirement witness. It verifies that a CSR read sees the pre-write value, the write commits once with provider acceptance, and the retirement record remains held until consumed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 CSR product-cycle evidence

Exercises a concrete RV32 Zicsr/Zifencei product through generated VHDL and a clocked CSR access/commit/retirement witness. It verifies that a CSR read sees the pre-write value, the write commits once with provider acceptance, and the retirement record remains held until consumed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/02_requirements/feature/riscv_gen2_hwir_foundation.md |
| Plan | doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md |
| Design | doc/05_design/riscv_gen2_hwir_foundation.md |
| Research | doc/01_research/local/riscv_gen2_hwir_foundation.md |
| Source | `test/02_integration/compiler/riscv_scalar_csr_product_cycle_ghdl_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises a concrete RV32 Zicsr/Zifencei product through generated VHDL and a
clocked CSR access/commit/retirement witness. It verifies that a CSR read sees
the pre-write value, the write commits once with provider acceptance, and the
retirement record remains held until consumed.

## Audience

Use this scenario when changing CSR ownership, scalar product composition,
retirement holding, or the VHDL interface of the closed CSR product.

## Preconditions

- A VHDL-2008-capable GHDL runner is available.
- The strict RV32 Zicsr/Zifencei scalar product compiler is available from the
  source under test.

## Workflow

1. Require GHDL; absence is a blocked test failure, never a skip.
2. Compile the fixed CSRRS instruction through the strict scalar product.
3. Analyze, elaborate, and simulate the generated product plus testbench.
4. Verify lookup, single atomic commit, held retirement, and one-time consume.

## Examples

- The fixed CSRRS instruction reads `mstatus` at address `0x300`.
- The read witness observes `0x000000A5` before the write commits.
- The accepted write carries `0x00000055` exactly once.
- The held retirement record retains the pre-write value until `retire_ready`.

## Captured evidence

The scenario captures execution, generated-artifact, and log evidence for the
one fixed configuration. The transient VHDL path is diagnostic-only and must
not be copied into a qualification directory by hand. A qualifying run uses
the admitted qualification producer to bind these inputs to compiler identity.

## Review checklist

Before accepting a diagnostic result, confirm that:

- GHDL availability is asserted before product construction.
- The product configuration is concrete RV32 Zicsr/Zifencei.
- CSR lookup has the expected address and read-enable signal.
- The write commit occurs once, with the expected address and value.
- Retirement sees the pre-write read value and no trap.
- Backpressure holds the record without repeating the commit.
- One ready handshake consumes retirement with no protocol fault.

## Evidence boundary

This is development-stage host evidence. It is not an admitted self-hosted
qualification receipt, full CSR ISA proof, privilege-mode proof, or a complete
processor claim. The qualification runner must retain compiler, VHDL, manifest,
and GHDL receipts separately.

## Failure handling

On failure, retain the transient `/tmp/scalar_csr_product_cycle.vhd` diagnostic
artifact and inspect the analyzer or simulator output. Do not weaken the fixed
CSR instruction, expected pre-write value, or exact-one-commit assertions.

## Compatibility and limitations

The test covers one supervisor-mode input witness only; it does not establish
all CSR addresses, read-modify-write variants, privilege exceptions, interrupt
arbitration, or hardware timing. It is compatible with the closed scalar
product route only. A legacy VHDL path, a host-only CSR oracle, or a manually
edited VHDL fixture is not equivalent evidence.

The testbench intentionally uses no external memory or fetch logic. Future
full-core evidence must compose the verified CSR owner with dispatch, decode,
trap, and retirement infrastructure under the same admitted toolchain.

## Operator handoff

When this scenario passes on an admitted toolchain, retain the generated VHDL,
the exact testbench text, analyze/elaborate/run logs, compiler identity, and
product manifest in the qualification envelope. A green developer-host result
must remain diagnostic until the qualification writer validates and publishes
the bound receipt. If GHDL is unavailable, preserve the blocked result and
resume only after the host dependency is installed; never turn this row into a
skip or a source-text-only assertion.

The receipt must record target profile, configuration identity, graph digest,
and exact GHDL command outcomes. Missing any one of those fields leaves this
scenario as planned qualification evidence rather than a release result.
The required receipt writer is the sole promotion authority.

**Requirements:** doc/02_requirements/feature/riscv_gen2_hwir_foundation.md

**Plan:** doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md

**Design:** doc/05_design/riscv_gen2_hwir_foundation.md

**Research:** doc/01_research/local/riscv_gen2_hwir_foundation.md

## Scenarios

### RISC-V Gen2 integrated CSR product cycle evidence

<details>
<summary>Advanced: should commit one CSR write atomically then hold one retirement</summary>

#### should commit one CSR write atomically then hold one retirement _(slow)_

- Require the external GHDL VHDL-2008 cycle runner
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: available is true
- Build and simulate the closed CSR product-cycle witness
   - Log capture: after_step
   - Evidence: log output verified by 5 expected checks
   - Expected: emitted.is_success() is true
   - Expected: vhdl_write_file(path, emitted.vhdl + "\n" + csr_product_tb()) is true
   - Expected: ghdl_analyze(path).success is true
   - Expected: ghdl_elaborate("scalar_csr_product_cycle_tb").success is true
   - Expected: ghdl_run("scalar_csr_product_cycle_tb", Some("500ns")).success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the external GHDL VHDL-2008 cycle runner")
val available = ghdl_available()
expect(available).to_equal(true)
if not available:
    val blocked = "BLOCKED: GHDL VHDL-2008 runner is unavailable; cannot satisfy REQ-G2-012/016"
    print blocked
    fail(blocked)
    return
step("Build and simulate the closed CSR product-cycle witness")
val emitted = compile_strict_riscv_scalar_product("scalar_csr_product_cycle",
    CoreConfig.rv32_zicsr_zifencei(), 0x300092F3,
    LsuConfig.rv32_product_default())
expect(emitted.is_success()).to_equal(true)
if emitted.is_success():
    val path = "/tmp/scalar_csr_product_cycle.vhd"
    expect(vhdl_write_file(path, emitted.vhdl + "\n" + csr_product_tb())).to_equal(true)
    expect(ghdl_analyze(path).success).to_equal(true)
    expect(ghdl_elaborate("scalar_csr_product_cycle_tb").success).to_equal(true)
    expect(ghdl_run("scalar_csr_product_cycle_tb", Some("500ns")).success).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- **Plan:** `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- **Design:** `doc/05_design/riscv_gen2_hwir_foundation.md`
- **Research:** `doc/01_research/local/riscv_gen2_hwir_foundation.md`


</details>
