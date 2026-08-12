# RISC-V Gen2 System Spec Truncated During Shared-Worktree Migration

Status: resolved — self-hosted qualification remains open

## Observation

During the shared-worktree migration,
`test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl` was
temporarily found as an untracked 99-line file containing VHDL testbench
helpers but no `describe` or executable `it` scenario. The full scenario has
since been restored in the same path. It now covers strict product routing,
compressed rows, source-less products, and RV32/RV64 64-bit-lineage protocol
vectors.

## Safety impact

The restored scenario removes the zero-scenario coverage hazard. Qualification
remains false because the available `bin/simple` is a Rust bootstrap seed, and
the common-Zca manifest intentionally retains `target_evidence_complete=false`
until the self-hosted product route and generated-VHDL/GHDL receipts run.

## Containment

- The restored scenario is the canonical system-level foundation spec and
  preserves its explicit source-less-product and RV32/RV64 protocol vectors.
- `test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl`
  independently checks closure-hash/header/lineage binding for the RV32
  stateful and RV64 trap-stateful compiler products.
- No release or mission-critical claim may treat bootstrap execution of either
  scenario as a qualification receipt.

## Unblock condition

The scenario restoration portion is complete. The remaining qualifying action
is to run it with a provenance-admitted self-hosted Simple runtime and the
generated RV32/RV64 GHDL lane, retain the receipts, update the matching manual,
and only then consider `row_target_evidence_complete` for promotion.

Owner: RISC-V Gen2 verification lane
