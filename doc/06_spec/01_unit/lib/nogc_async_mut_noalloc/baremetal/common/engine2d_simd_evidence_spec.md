# SimpleOS Engine2D SIMD Evidence Contract

## Scenario: admit executed target SIMD only

1. Construct an x86_64 AVX2 producer receipt with positive dispatches, vector
   chunks and lanes for fill, copy, alpha, alpha-edge, scroll, and diagram.
2. Give every operation a positive checksum, exact scalar/SIMD checksum parity,
   zero mismatches, and zero scalar fallback calls.
3. Confirm the shared validator accepts the receipt.
4. Independently remove vector execution, introduce fallback, change parity,
   add mismatches, or remove diagram execution; each mutation must fail.

## Scenario: reject unsupported or unlinked targets

1. Change an x86 receipt to NEON and confirm it fails.
2. Mark the target intrinsic owner unlinked and confirm it fails.
3. Construct the explicit unsupported RVV blocker and confirm it cannot pass or
   expose a positive framebuffer checksum.

These are pure contract checks. Native instruction and QEMU evidence remain
separate mandatory gates.
