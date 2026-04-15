<!-- codex-research -->
# Domain Research: x86 Dual-Arch QEMU Boot

## Scope

Collect external guidance for a stable x86 plan that supports both 32-bit and 64-bit lanes under QEMU.

## Findings

### 1. QEMU `-kernel` is documented as direct Linux boot, not a generic x86 kernel loader

QEMU documents `-kernel` under "Direct Linux Boot" and describes it as a fast way to boot Linux kernels directly without a full bootable image.

Implication:

- `-kernel` should not be treated as the generic correctness model for all custom x86 kernels.
- For non-Linux x86 kernels, a real boot protocol and bootable image contract matters more than the convenience of the QEMU flag.

Source:

- QEMU Direct Linux Boot: https://qemu.readthedocs.io/en/v9.1.3/system/linuxboot.html

### 2. Multiboot1 is a 32-bit boot contract

GRUB Multiboot v0.6.96 explicitly targets free 32-bit operating systems and says the OS image should be an ordinary 32-bit executable with a Multiboot header.

Implication:

- A 64-bit kernel using Multiboot1 still naturally begins with a 32-bit-compatible boot entry/header.
- The expected model is "32-bit boot stub first, then runtime mode transition if needed."

Source:

- GRUB Multiboot specification: https://www.gnu.org/software/grub/manual/multiboot/multiboot.html

### 3. Multiboot2 still centers BIOS/i386 handoff on 32-bit protected mode

The Multiboot2 header `architecture` field uses `0` for 32-bit protected mode of i386.

Implication:

- Even Multiboot2 does not imply "native 64-bit BIOS handoff by default."
- A dual-lane x86 design should keep the 32-bit-compatible boot contract explicit.

Source:

- GRUB Multiboot2 specification: https://www.gnu.org/software/grub/manual/multiboot2/multiboot.html

### 4. 64-bit-native entry is an EFI-specific path in Multiboot2

Multiboot2 defines separate EFI i386 and EFI amd64 entry-address tags. The amd64 entry tag is used only on EFI amd64 platforms with EFI boot services.

Implication:

- A real 64-bit-native boot lane should be treated as a separate EFI/64-bit path, not assumed to fall out of the BIOS/Multiboot1 style path.
- This supports a design where:
  - BIOS/Multiboot stays 32-bit-compatible
  - 64-bit-native entry remains a distinct path

Source:

- GRUB Multiboot2 specification: https://www.gnu.org/software/grub/manual/multiboot2/multiboot.html

### 5. QEMU defaults already distinguish x86_32 and x86_64 guest CPU lanes

QEMU documents `qemu32` and `qemu64` as the default virtual CPU models for i686 and x86_64 guests.

Implication:

- The validation matrix should treat CPU model and guest architecture as first-class differences.
- The plan should keep:
  - `qemu-system-i386 -cpu qemu32`
  - `qemu-system-x86_64 -cpu qemu64`
  as separate lanes.

Source:

- QEMU x86 system emulator docs: https://qemu.eu/doc/6.0/system/target-i386.html

## Synthesis

The external model strongly supports:

- a 32-bit-compatible boot entry for BIOS/Multiboot boot
- an optional 64-bit runtime transition after boot
- a separate 64-bit-native entry path only when using an explicitly 64-bit boot environment such as EFI amd64

That aligns with a repo plan that supports both x86_32 and x86_64, but does not force one lane to masquerade as the other.
