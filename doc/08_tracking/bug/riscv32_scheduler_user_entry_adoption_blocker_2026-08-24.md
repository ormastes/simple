# RV32 scheduler user-entry adoption blocker — 2026-08-24

The first isolated Sv32 mapper draft was rejected and removed. Static review
found that a copyable owner could be forged or double-destroyed, an Armed
identity snapshot could become stale, and rollback freed frames even after an
unmap failure, leaving a live PTE to reusable memory. The draft also mapped
read-only data executable and lacked complete physical-address validation.

Global RV32 process-image readiness remains false. A safe implementation needs:

- a module-private bounded registry with generation/nonce-sealed handles;
- a live loader joint reservation held across mapping and adoption;
- distinct lower-half root mutation with full Sv32 physical-range validation;
- reverse rollback that retains failed PTE/frame pairs in a recoverable
  quarantine and never frees a still-mapped frame;
- independent R/W/X flags, page-zero rejection, and checked arithmetic;
- confirmation that traps do not need low UART/PLIC/CLINT identities after the
  user SATP is installed;
- a checked U-mode context constructor that rejects truncation, followed by
  scheduler-owned one-shot SATP installation and `sret` transfer.

The RV32 stack policy/default selector has been moved from `0x81000000`
(copied kernel root index 516) to `0x7ffff000` in the disjoint user half. This
is not yet an operational RV32 process-image path: the canonical ELF builder
still rejects RV32 and invokes the stack builder with an eight-byte word size.
It must admit RV32 and select the already-available four-byte serializer.

No tests, builds, SPipe, benchmarks, optimizer, bootstrap, or runtime
verification were run for this change, per user instruction.
