# RISC-V sharing receipt accepts unverified inventory labels

Status: fixed and verified

The generic signed external-evidence validator authenticates the reviewer and
the exact observation blobs, but the `riscv32-riscv64-shared` lane previously
accepted its five PASS labels without proving that an ownership inventory was
complete or matched committed source. A signed omission, stale path list, or
unjustified architecture-only leaf could therefore satisfy the generic schema.

The fix adds a lane-specific committed-tree validator. It inventories every
owned `src` path whose name identifies RISC-V/RV32/RV64, requires an exhaustive
disjoint shared/RV32/RV64 classification, requires bilateral existing consumer
references for shared rows, and requires explicit specialization reasons for
architecture-only rows. This hardens evidence admission; it does not claim the
current broader RISC-V implementation has achieved the sharing target.

Acceptance requires a valid signed exact inventory to pass and signed missing,
stale, duplicate, unsorted, nonexistent, or unjustified evidence to fail.

The focused must-check contract passed once after the final semantic correction
in 11.14 seconds with a 0-second committed-ref subpath and 6,656 KiB peak RSS.
It exercised a valid signed inventory plus signed missing attachment, stale
path, unjustified specialization, and same/cross-class bilateral mutations.
Independent review found no remaining inventory-admission bypass.
