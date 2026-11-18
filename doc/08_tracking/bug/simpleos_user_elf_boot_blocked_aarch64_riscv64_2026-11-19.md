# SimpleOS aarch64/riscv64 user ELFs: no boot lane, and internal-link layout divergences

- status: open
- found: 2026-11-19 (lane ssos)

## Boot blocker (not a linker defect)
No in-tree lane runs a filesystem-loaded user ELF on aarch64 or riscv64:
- `check-simpleos-aarch64-hello-world-in-guest-efi.shs` (AAVMF): program runs at EL1;
  no aarch64 EL0 map+enter path in the Limine lane.
- `check-simpleos-riscv64-hello-world-in-guest-opensbi.shs` (OpenSBI fw_payload):
  program runs in S-mode; `_rv64_enter_user` exists but needs the scheduler + ELF
  loader closure.
Both also need the Rust seed (`SIMPLE_BIN`), absent in this WSL host.
So the internally linked user ELFs from `link_simpleos_user_64` cannot be booted yet.

## llvm-readelf comparison, internal vs ld.lld (C hello + sysroot libsimpleos_all.a)
Same on both arches: ELF type EXEC, e_machine, e_entry (0x50000000 / 0x100000000),
e_flags (rv64 0x5 RVC|double), RX and R PT_LOADs (same size), .text/.rodata sizes.
Divergences:
1. Synthesized `.got` (orphan) is placed after `.bss`; lld places it after `.data`.
   Effect: `.bss` becomes file-backed (rw PT_LOAD filesz=memsz ~0x1ace8).
2. One extra empty `R` PT_LOAD for the empty .init_array/.fini_array/.tdata/.tbss run.
3. riscv64 `.got` is 0x18 vs lld 0x20 (lld reserves the GOT[0] header slot).
4. aarch64 `.rodata` 0x388 vs lld 0x385 (tail alignment padding).
5. Archive-member order differs, so function addresses differ (same set, same sizes).
None of these stops a static image from loading, but 1 inflates the file and should
follow lld's orphan placement.
