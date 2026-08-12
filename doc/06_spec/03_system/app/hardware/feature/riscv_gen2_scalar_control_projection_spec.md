# RISC-V Gen2 Scalar Control Projection — System Scenario

## Purpose and audience

This scenario checks the narrow compiler-to-VHDL projection for the exact JALR
parcel `0xFFF082E7`. It emits independent RV32 and RV64 typed projections and
checks that each generated VHDL payload clears JALR bit zero through the typed
`control_target` graph. It is for compiler and hardware maintainers reviewing
projection evidence.

The scenario is stateless compiler projection evidence only. It does not prove
an architectural control path, a scalar processor, or target qualification.

## Preconditions

- Run `test/03_system/app/hardware/feature/riscv_gen2_scalar_control_projection_spec.spl`.
- GHDL is optional. When present, it must support `ghdl -a --std=08`.
- The generated analyzer inputs are
  `/tmp/riscv_scalar_control_rv32.vhd` and
  `/tmp/riscv_scalar_control_rv64.vhd`.

## Operator workflow

### Should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available

1. Compile the exact RV32 and RV64 JALR bit-clear projection products from
   `0xFFF082E7`.
2. Require both compiler products to succeed and to contain the generated
   `control_target <= raw_target and target_mask;` statement.
3. Probe `ghdl --version` once.
4. If the probe succeeds, write both generated VHDL artifacts and analyze each
   with `ghdl -a --std=08`.
5. If the probe fails, record the visible named skip `GHDL VHDL-2008 analyzer
   unavailable`, including its exit code. The generated-VHDL assertions remain
   host evidence; this does not claim GHDL analysis.

## Evidence and provenance

- **Executable-command evidence:** one `ghdl --version` availability probe and,
  when present, two VHDL-2008 analyzer invocations.
- **Artifact evidence:** the generated RV32 and RV64 VHDL files in `/tmp`,
  written only immediately before the external analyzer runs.
- **Source boundary:**
  `compile_strict_riscv_scalar_control_projection_product` emits both payloads;
  the scenario does not use handwritten VHDL or a legacy route.

## Requirement traceability

| Requirement | Scenario evidence |
|---|---|
| REQ-G2-001 | Both projections are constructed through the typed Gen2 product API. |
| REQ-G2-002 | RV32 and RV64 are selected as concrete elaboration-time configurations. |
| REQ-G2-003 | Both generated typed VHDL payloads are analyzed with GHDL when available. |
| NFR-G2-006 | The emitted JALR target graph visibly masks bit zero in both products. |

## Scorecard and remediation

| Check | Pass condition | On failure |
|---|---|---|
| Product emission | Both products succeed | Treat as a typed control-projection compiler failure. |
| Target masking | Both VHDL payloads contain the typed target-mask assignment | Fix strict HWIR lowering; do not replace it with VHDL text fixtures. |
| GHDL availability | Probe succeeds, or a named skip records its exit code | Install/configure GHDL to obtain external analysis evidence. |
| External analysis | Both `ghdl -a --std=08` calls exit zero | Inspect the retained `/tmp` artifacts and GHDL diagnostics. |

## Compatibility and limitations

The GHDL branch is conditional because the analyzer is an external host tool.
An unavailable analyzer produces an explicit named skip rather than a passing
tautological assertion. This scenario is combinational VHDL analysis only; it
does not elaborate a testbench, simulate a pipeline, or qualify hardware.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-G2-001 REQ-G2-002 REQ-G2-003 NFR-G2-006
# @capture exec
# @capture artifact
it "should analyze concrete RV32 and RV64 JALR bit-clear graphs when GHDL is available":
    step("Compile the exact RV32 and RV64 JALR bit-clear projection products")
    step("Probe the required GHDL VHDL-2008 analyzer once")
    # The executable source contains the complete assertions, artifact writes,
    # GHDL analysis branch, and explicit unavailable-analyzer skip.
```

</details>
