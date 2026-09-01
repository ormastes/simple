# RISC-V Gen2 Atomic Extension: NFR Options

Date: 2026-08-12
Status: Pending Selection

## Option 1 — External atomic authority (recommended)

Require a typed request/response interface whose downstream owner guarantees
indivisible RMW and reports reservation invalidation. Gen2 never synthesizes an
AMO from separate ordinary LSU operations.

- Pros: honest across cache, fabric, multi-hart, DMA, and MMIO boundaries.
- Cons: requires a capable cache/bus adapter.
- Effort: high.

## Option 2 — Private-cache authority

Bind atomicity to a compiler-owned private cache/reservation controller.

- Pros: stronger local implementation control and formal state visibility.
- Cons: couples the scalar product to cache geometry and coherence design.
- Effort: very high.

## Option 3 — Single-hart local reservation only

Support only locally observed stores and document no coherent external writers.

- Pros: smallest FPGA implementation.
- Cons: unsuitable for mission-critical multi-master systems and cannot support
  the requested general Gen2 product direction.
- Effort: medium.
