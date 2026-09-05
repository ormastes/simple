<!-- codex-research -->
# NFR Options: x86 Dual-Arch QEMU Boot

## NFR Option 1: Minimal Stability Gate

Description:

- Require only:
  - deterministic serial markers
  - correct QEMU target per arch
  - no early `FAULT @` before first marker

Pros:

- Fastest to implement.
- Good for early bring-up.

Cons:

- Too weak for long-term regression control.

Effort:

- S, about 3-5 files

## NFR Option 2: Recommended Dual-Arch Validation Gate

Description:

- Require:
  - deterministic serial markers
  - explicit x86_32 vs x86_64 QEMU tuples
  - no early fault before first marker
  - one passing probe lane on x86_32
  - one passing full runtime/browser lane on x86_64
  - no silent spec caching for QEMU validation

Pros:

- Balanced and testable.
- Matches the proposed split-lane architecture.

Cons:

- More harness work than the minimal gate.

Effort:

- M, about 5-8 files

## NFR Option 3: Strong Release Gate

Description:

- Require all of Option 2 plus:
  - framebuffer/screenshot verification
  - direct ad hoc QEMU command verification outside the spec runner
  - per-lane boot-time budget and marker timing targets

Pros:

- Strong regression protection.
- Suitable for release gating.

Cons:

- Higher maintenance cost.
- Slower CI/runtime verification.

Effort:

- L, about 8-12 files

## Recommendation

Recommended: NFR Option 2

Reason:

- Strong enough to keep x86_32 and x86_64 honest without turning the first stabilization pass into a full release-grade boot lab.
