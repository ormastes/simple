# RISC-V Gen2 Scalar ALU Retire Projection — System Scenario

## Purpose and audience

This operator-facing scenario checks a narrow compiler-to-VHDL boundary: the
RV32 `ADDI 0xFFF08293` vector must be represented by an exact 32-bit VHDL
literal, rather than an overflowing host `INTEGER` conversion. It is for
compiler and hardware maintainers reviewing generated VHDL evidence.

The scenario is development-stage projection evidence only. It does not prove
architectural retirement, a complete scalar core, or processor qualification.

## Preconditions

- Run the executable source at
  `test/03_system/app/hardware/feature/riscv_gen2_scalar_alu_projection_spec.spl`.
- GHDL is optional. When present, it must support `ghdl -a --std=08`.
- The generated analysis artifact is `/tmp/riscv_gen2_scalar_addi_high_bit.vhd`.

## Operator workflow

### Should analyze the RV32 ADDI `0xFFF08293` vector without INTEGER overflow when GHDL is available

1. Compile the exact RV32 high-bit ADDI scalar ALU retire projection.
2. Inspect the generated VHDL for the exact-width literal
   `11111111111100001000001010010011` and reject the unsafe
   `to_unsigned(4293952147` form.
3. Probe `ghdl --version` once.
4. If the probe succeeds, write the generated VHDL artifact and analyze it
   with `ghdl -a --std=08`.
5. If the probe fails, record a visible skip named `GHDL VHDL-2008 analyzer
   unavailable`, including the probe exit code. The emitted-VHDL assertions
   remain host evidence; no GHDL analysis claim is made.

## Evidence and provenance

- **Executable-command evidence:** the single `ghdl --version` availability
  probe and, when available, `ghdl -a --std=08`.
- **Artifact evidence:** `/tmp/riscv_gen2_scalar_addi_high_bit.vhd`, written
  only before the external analyzer is invoked.
- **Source boundary:** `compile_strict_riscv_scalar_alu_retire_projection_product`
  emits the projection under test; the scenario does not substitute a fixture
  or handcrafted VHDL payload.

## Requirement traceability

| Requirement | Scenario evidence |
|---|---|
| REQ-G2-001 | The exact RV32 product compiles successfully. |
| REQ-G2-002 | The high-bit ADDI vector emits a 32-bit exact-width instruction literal. |
| REQ-G2-003 | Available GHDL performs VHDL-2008 analysis of the generated artifact. |
| NFR-G2-006 | The unsafe host-integer conversion form is explicitly absent. |

## Scorecard and remediation

| Check | Pass condition | On failure |
|---|---|---|
| Product emission | Compilation succeeds | Treat as a compiler projection failure. |
| Literal safety | Exact 32-bit literal is present and unsafe conversion absent | Fix VHDL lowering; do not change the vector. |
| GHDL availability | Probe succeeds, or a named skip records its exit code | Install/configure GHDL to obtain analysis evidence. |
| External analysis | `ghdl -a --std=08` exits zero | Inspect the retained `/tmp` VHDL artifact and analyzer diagnostics. |

## Compatibility and limitations

The GHDL branch is conditional because the analyzer is an external host tool.
An unavailable analyzer is explicitly skipped, not converted into a passing
analysis assertion. This scenario is combinational VHDL analysis only; it does
not elaborate a testbench, simulate retirement behavior, or qualify hardware.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-G2-001 REQ-G2-002 REQ-G2-003 NFR-G2-006
# @capture exec
# @capture artifact
it "should analyze the RV32 ADDI 0xFFF08293 vector without INTEGER overflow when GHDL is available":
    step("Compile the exact RV32 high-bit ADDI scalar ALU retire projection")
    # The executable source contains the complete assertions and conditional
    # GHDL availability branch.
```

</details>
