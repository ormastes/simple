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

## Update 2026-11-19: divergences 1-3 fixed (verification-pending)
Root cause of 1: the SimpleOS user script names `.got : { *(.got) *(.got.*) }` after
`.data`; the engine ignored it (the synthetic GOT has no input sections) and appended
.got after .bss. Fix in `elf_boot_link.spl`:
- the synthetic GOT fills a script `.got` output section when one exists (fail closed if
  real input .got sections also land there); otherwise the old orphan position;
- riscv64 reserves ld.lld's one .got header slot (0 in a static image);
- an empty output section joins the current PT_LOAD (lld inherits flags), and a new
  PT_LOAD opens at relroEnd (first section after the last .got/init/fini/TLS one), as lld.
Spec: `elf_boot_link_got_spec` (fixtures `test/fixtures/linker/elf/got_orphan/`), oracle
= llvm-readelf of ld.lld 18. Re-run on the hello: riscv64 sections identical to lld,
both arches 4 PT_LOADs with identical RX/R/RW(data) and NOBITS .bss.
Still cosmetic: lld starts the .bss PT_LOAD at the empty .tbss boundary (same end
address); aarch64 .rodata tail padding (0x388 vs 0x385); archive member order.
