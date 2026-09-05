# RISC-V Gen2 Atomic Extension: Feature Options

Date: 2026-08-12
Status: Pending Selection

## Option A — Full A owner (recommended)

Implement LR.W/SC.W and all word AMOs for RV32/RV64, plus RV64 LR.D/SC.D and
doubleword AMOs, in one typed provider and database/profile family.

- Pros: complete coherent A product; one reservation and atomic-bus contract.
- Cons: largest initial verification matrix and bus integration.
- Effort: high.

## Option B — Zalrsc first

Implement LR/SC and reservation invalidation first; add Zaamo later.

- Pros: smaller state machine; enables canonical lock loops early.
- Cons: cannot advertise A; leaves common AMO workloads unsupported.
- Effort: medium.

## Option C — Zaamo first

Implement atomic fetch-and-op rows first with no LR/SC reservation state.

- Pros: straightforward external atomic transaction interface.
- Cons: cannot advertise A; no compare/exchange loop primitive.
- Effort: medium.
