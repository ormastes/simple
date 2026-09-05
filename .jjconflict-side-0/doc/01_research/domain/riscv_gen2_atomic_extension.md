# RISC-V Gen2 Atomic Extension: Domain Research

Date: 2026-08-12
Status: requirement selection pending

## Normative basis

RISC-V A 2.1 consists of Zaamo plus Zalrsc. Atomic instructions carry `aq` and
`rl` ordering bits. LR establishes a reservation set; SC succeeds only when its
address/size remains covered and always invalidates the hart reservation. AMOs
atomically return the old value and publish the computed new value. RV64 word
forms sign-extend their architectural result. Misaligned or access-faulting
atomics must not partially modify memory.

Primary sources:

- https://docs.riscv.org/reference/isa/v20240411/unpriv/a-st-ext.html
- https://docs.riscv.org/reference/isa/unpriv/mm-formal.html
- https://docs.riscv.org/reference/isa/unpriv/rv-32-64g.html

## Architecture implication

The typed boundary must make atomicity external and falsifiable: request kind,
address, width, operands, aq/rl, transaction identity, response old value,
SC-success, fault, and reservation invalidation are explicit. The owner holds
the complete event until atomic response acceptance and routes exactly one
normalized completion through trap and retirement.
