# Simple linker could not link riscv64 bare-metal / boot images

- **Status:** verification-pending
- **Date:** 2026-11-18
- **Lane:** sbm-rv64
- **Area:** `src/compiler/70.backend/linker/elf/elf_boot_link.spl`,
  `src/compiler/70.backend/linker/elf/riscv_align.spl`

## Symptom

`elf_boot_link` (the in-house linker-script ELF linker for bare-metal and
SimpleOS images) rejected every riscv64 link with
`elf_boot_link: supports only x86_64 and aarch64 targets`, so
`check-baremetal-efi-boot.shs --arch riscv64 --linker simple` could not link.

## Root cause

1. `_bl_machine` had no `Riscv64` arm (EM_RISCV 243).
2. `R_RISCV_PCREL_LO12_I/S` name a label on the AUIPC that carries the paired
   `PCREL_HI20`/`GOT_HI20`; the boot linker applied each relocation alone and
   `reloc_apply` (correctly) refuses an unpaired PCREL_LO12.
3. x86-only branches were written as `not a64`, so they would also fire for
   RISC-V types sharing a number (25 = x86 GOTOFF64 = RISC-V PCREL_LO12_S,
   27 = x86 GOT64 = RISC-V LO12_I).
4. e_flags (RVC / float ABI) were never written.
5. Similar pattern found in the shared `riscv_align.spl` (also used by
   `elf_static_link`): R_RISCV_ALIGN padding was refilled with all `c.nop`
   on RVC objects, while ld.lld writes one `c.nop` (if 2 mod 4) then 4-byte
   `nop`s. Functionally equal, but not byte-identical to lld.

## Fix

- New shared module `src/compiler/70.backend/linker/riscv_reloc.spl` (HI20
  site key, PCREL_LO value, LO12 type mapping); `elf_static_link` uses it too,
  so riscv32 / SimpleOS reuse one implementation.
- `elf_boot_link`: Riscv64 machine; merged e_flags via `elf_riscv_flags`;
  `elf_riscv_align_objects`; RELAX ignored (relaxation off = `ld.lld
  --no-relax`); PCREL_LO12 applied after all HI20 values are known;
  x86-only branches gated on x86; RISC-V TLS rejected fail-closed in boot
  images.
- `riscv_align.spl`: lld nop fill order.
- `check-baremetal-efi-boot.shs --linker simple`: the lld layout reference for
  riscv uses `--no-relax`.

## Tests

- `test/01_unit/compiler/backend/linker/elf_boot_link_riscv64_spec.spl`
  (fixtures `test/fixtures/linker/elf/riscv_boot/`): CALL_PLT, PCREL_HI20 +
  LO12_I + LO12_S, HI20/LO12_I, JAL, RVC_BRANCH, R_RISCV_64, RELAX and ALIGN;
  bytes equal `ld.lld --no-relax` (LLD 18); out-of-range absolute HI20 is an
  Err; a machine mismatch is an Err. Fails before (riscv64 rejected), 6/6 after.
- `elf_static_link_spec.spl` 7/7 (shares riscv_align / riscv_reloc).
- Pending evidence: OpenSBI real-firmware boot
  `sh scripts/check/check-baremetal-efi-boot.shs --arch riscv64 --linker simple`
  (queued in the shared one-lane slot).
