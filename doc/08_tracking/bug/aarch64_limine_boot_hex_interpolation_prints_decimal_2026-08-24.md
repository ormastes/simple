# `0x{value}` interpolation prints DECIMAL in the aarch64 Limine boot log

Status: OPEN (cosmetic, but actively misleading)
Found: 2026-08-24, lane K, while landing the first real-firmware aarch64 SimpleOS boot.

## Symptom

Real serial transcript, `qemu-system-aarch64 -M virt` under EDK2/AAVMF pflash
via Limine `BOOTAA64.EFI`:

```
[BOOT] HHDM offset: 0x18446462598732840960
[BOOT] Framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200
[BOOT] Kernel: phys=0x1604648960 virt=0x18446744071563116544
```

`18446462598732840960` is `0xFFFF800000000000` written in base 10. The `0x`
prefix is a literal in the format string; the interpolated value is rendered by
the decimal formatter (`rt_raw_u64_to_string` / `rt_raw_i64_to_string`), so
every address in this log reads as a nonsense decimal with a hex prefix.

## Where

`src/os/kernel/boot/limine_boot_aarch64.spl` — every `0x{...}` interpolation
(HHDM offset, region base/size, framebuffer addr, RSDP, kernel phys/virt).
The x86_64 twin `limine_boot.spl` has the same pattern.

## Why it is not "just cosmetic"

The boot log is the ONLY evidence channel for this lane, and the gate
`scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` quotes it. An
address that cannot be compared against a datasheet or a QEMU memory map by eye
degrades the evidence. It also silently hides bit patterns (leading nibbles).

## Fix direction

There is no hex formatter in the freestanding runtime — only
`rt_write_decimal`. Add `rt_raw_u64_to_hex_string` to
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c` (and
the C runtime for parity) and give Simple a hex interpolation form, OR call the
formatter explicitly at each site. Deliberately NOT done in the same pass as
the boot bring-up so the boot change stays reviewable.
