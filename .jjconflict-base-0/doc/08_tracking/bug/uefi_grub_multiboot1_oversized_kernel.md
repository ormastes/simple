# BUG: GRUB-EFI multiboot1 faults loading the oversized merged ring-3 kernel

**Status:** RESOLVED 2026-07-11 — merged ring-3 kernel now boots under OVMF to
`[sshd] accept loop start` and completes the `ssh root@127.0.0.1 /FSEXEC.ELF`
bonus (`hello from clang on simpleos` + `[user] exit rc=42`). Fix: relink the
kernel load base from 1MB (`0x100000`) to 128MB (`0x8000000`) in
`examples/09_embedded/simple_os/arch/x86_64/linker.ld`. Root cause: the merged
image (~23MB text + 236MB BSS) filled the low region [1MB, ~237MB], starving
GRUB-EFI's multiboot1 relocator of a safe low trampoline slot → it faulted (#UD
at RIP~0x1012, in long mode, before kernel `_start`). Loading at 128MB leaves
[1MB,128MB) free for GRUB's relocator; the crt0 identity map already covers the
first 4GiB and QEMU `-kernel` honours `p_paddr`, so both boot paths verified
green (accept loop + hello + rc=42).
**Severity:** medium (the ring-3 demo boots fine under QEMU `-kernel`; this only
blocks the ring-3 `hello+rc=42` bonus under real UEFI firmware)
**Component:** boot — GRUB-EFI multiboot1 handoff / kernel LOAD-segment layout
**Found:** 2026-07-11 (UEFI board-boot bring-up)

## What works

A full SimpleOS SSH kernel boots under **real UEFI firmware (OVMF)** end to end:
OVMF → EFI System Partition → `EFI/BOOT/BOOTX64.EFI` (a `grub-mkstandalone`
image with `grub.cfg` + the kernel embedded in its memdisk) → GRUB multiboot1 →
kernel `_start` → `[sshd] accept loop start`, and it accepts an inbound host ssh
client. Evidence: `build/os/uefi_acceptloop_evidence.serial.log`. Repro:
`scripts/os/ssh_ring3_uefi_boot.shs`. ESP is served to OVMF via QEMU VVFAT
(`-drive file=fat:rw:$ESP`) on a virtio-blk disk — no xorriso/mtools/root needed.
OVMF: split pflash `/usr/share/OVMF/OVMF_CODE_4M.fd` + writable `OVMF_VARS_4M.fd`.

## The blocker

The **merged ring-3-exec kernel** `build/os/simpleos_ssh_ring3.elf` (~23 MB,
a single 22.6 MB R-E LOAD segment at phys `0x100000`) makes GRUB's multiboot1
loader fault: `#UD Invalid Opcode` at `RIP=0x1012` (caught by OVMF's own X64
exception handler); kernel `_start` never runs.

Decisively isolated: the **identical** OVMF→GRUB→multiboot1 mechanism boots the
smaller SSH kernel (`ssh_live_32.elf`, ~2 MB text, same multiboot1 header, even
with a 236 MB BSS) all the way to the accept loop. So the fault is GRUB-EFI
multiboot1 relocation/placement of the oversized **text** segment in
firmware-reserved low memory — not the UEFI path, not BSS size.

## Fix directions

1. Add a **multiboot2 + EFI-handoff** header to the kernel and boot via GRUB
   multiboot2 (skips the low-memory multiboot1 relocation constraints).
2. **Relink** the kernel text higher (above the firmware-reserved low region)
   so the load target doesn't collide with OVMF-reserved pages.
3. **Shrink** the merged image (the 22.6 MB single R-E segment is unusually
   large — investigate why; split/strip).

## Gap to a physical board (separate)

OVMF proxies UEFI firmware but not hardware: real NIC driver (Intel/Realtek vs
virtio-net), real NVMe controller quirks vs QEMU's model, ACPI + framebuffer
(GRUB reports "no suitable video mode found"), and booting off a real GPT/ESP
USB stick rather than QEMU VVFAT.
