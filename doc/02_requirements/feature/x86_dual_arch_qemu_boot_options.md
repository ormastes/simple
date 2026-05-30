<!-- codex-research -->
# Feature Options: x86 Dual-Arch QEMU Boot

## Option A: Split-Lane x86 Design

Description:

- Treat x86_32 and x86_64 as separate boot/runtime lanes.
- x86_32 owns Multiboot/BIOS boot probes and minimal browser/desktop smoke.
- x86_64 owns long-mode wrapper, desktop, browser, and service integration.

Pros:

- Matches current repo structure.
- Lowest architectural risk.
- Avoids forcing x86_64 through a fake 32-bit packaging model as the primary design.
- Lets the team get a real passing x86_32 probe lane sooner.

Cons:

- Requires maintaining two wrapper/boot paths.
- Some test logic must be duplicated at the boot boundary.

Effort:

- M, about 8-12 files

## Option B: Unified Shared x86 Wrapper

Description:

- Build one shared wrapper model that tries to serve both x86_32 and x86_64 from one boot/runtime implementation.

Pros:

- Fewer boot-specific files on paper.
- Shared marker logic is centralized.

Cons:

- High risk of ABI leakage across 32-bit and 64-bit lanes.
- Fights the repo’s current structure.
- Likely to prolong the current x86_64 wrapper instability.

Effort:

- XL, about 15-25 files

## Option C: BIOS 32-bit Lane Plus Separate EFI 64-bit Lane

Description:

- Keep x86_32 as the BIOS/Multiboot lane.
- Build a separate x86_64-native EFI-oriented lane instead of relying on ELF32 wrapping.

Pros:

- Architecturally clean.
- Best long-term separation of boot contracts.
- Aligns with external Multiboot2/EFI guidance.

Cons:

- Larger bootloader/build-system change.
- More infrastructure work before browser validation benefits appear.

Effort:

- XL, about 18-30 files

## Recommendation

Recommended: Option A

Reason:

- It gives the fastest path to a stable boot matrix while still leaving room for Option C later if native 64-bit boot becomes a priority.
