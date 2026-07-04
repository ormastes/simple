# RISC-V Product Lean Regeneration Contract

`src/RiscvProduct/Generated.lean` is the regeneration-owned Lean file in this
project. `riscv_product.byl` is the matching regeneration-owned compact
proof-model surface.

Stable API expected by manual proofs:

- namespace: `RiscvProduct`
- inductives: `Lane`, `Abi`, `Mmu`, `FormalGate`
- structure: `ProductProfile`
- defs: `profile`, `withProductMetadata`, `withBudgets`, `nextLane`,
  `servedWithinTwo`, `ResourceState`, `acquire`, `release`

Stable BYL facts expected by tool gates:

- lanes: `rv32`, `rv64`
- product level: `linux-rtl`
- configuration profile: `qemu-virt+fpga-board`
- default budgets: RV32 `max_luts = 25000`, RV64 `max_luts = 45000`,
  both `target_mhz = 50`
- configurable fields: `product_level`, `configuration_profile`,
  `rv32.max_luts`, `rv64.max_luts`, `rv32.target_mhz`, `rv64.target_mhz`
- formal gate: `rvfi+sby`
- resource model: single-owner acquire/release
- scheduler model: round-robin with starvation bound `2`

Regeneration rule:

- Code changes may replace `Generated.lean`.
- Code changes may replace `riscv_product.byl`.
- Code changes must not replace `Constraints.lean`.
- If a stable name or theorem-facing constant changes, update
  `Constraints.lean` in the same change and run `lake build`.
- Pure implementation-body changes under the same names should leave
  `Constraints.lean` intact.
