# RISC-V Product Lean Regeneration Contract

`src/RiscvProduct/Generated.lean` is the regeneration-owned Lean file in this
project. `riscv_product.byl` is the matching regeneration-owned compact
proof-model surface.

Stable API expected by manual proofs:

- namespace: `RiscvProduct`
- inductives: `Lane`, `Abi`, `Mmu`, `FormalFlow`, `FormalGate`, `Readiness`
- structure: `ProductProfile` (fields `readiness`, `formalFlow`, `formalGate`)
- defs: `profile`, `Abi.isHardFloat`, `withProductMetadata`, `withBudgets`,
  `nextLane`, `servedWithinTwo`, `ResourceState`, `acquire`, `release`

Stable BYL facts expected by tool gates:

- lanes: `rv32`, `rv64`
- product level: `linux-rtl`
- configuration profile: `qemu-virt+fpga-board`
- default budgets: RV32 `max_luts = 25000`, RV64 `max_luts = 45000`,
  both `target_mhz = 50`
- configurable fields: `product_level`, `configuration_profile`,
  `rv32.max_luts`, `rv64.max_luts`, `rv32.target_mhz`, `rv64.target_mhz`
- ABI: RV32 `ilp32`, RV64 `lp64` — **soft-float**. The generated cores have no
  F/D unit, so a hard-float ABI (`ilp32d`/`lp64d`) is a false capability claim
  and `XLen.validate_isa_abi_consistency` rejects it.
- readiness: `contract-not-ready` (generated cores are placeholders)
- formal flow (the designated track): `formal_flow = "rvfi+sby"`
- formal gate (the current *result*): `formal_gate = "placeholder-rejected"`
- resource model: single-owner acquire/release
- scheduler model: round-robin with starvation bound `2`

Exports consumed by the manual proof layer (`Constraints.lean`): `abi`,
`readiness`, `formal_flow`, `formal_gate`, `max_luts`, `target_mhz`. Changing
any of these requires updating `Constraints.lean` in the same change.

Do not restore `formal_gate = "rvfi+sby"` or a hard-float ABI without RTL that
earns them: `no_profile_claims_a_passing_formal_gate`,
`unready_lanes_never_claim_a_passing_gate`, and `no_profile_claims_hard_float`
in `Constraints.lean` will refuse to compile.

Regeneration rule:

- Code changes may replace `Generated.lean`.
- Code changes may replace `riscv_product.byl`.
- Code changes must not replace `Constraints.lean`.
- If a stable name or theorem-facing constant changes, update
  `Constraints.lean` in the same change and run `lake build`.
- Pure implementation-body changes under the same names should leave
  `Constraints.lean` intact.
