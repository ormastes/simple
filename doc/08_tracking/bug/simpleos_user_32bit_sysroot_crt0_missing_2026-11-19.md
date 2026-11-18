# SimpleOS 32-bit userland: no sysroot, crt0 or syscall stub (i686, arm32, riscv32)

- **Status:** open
- **Date:** 2026-11-19
- **Lane:** ssos (Simple linker vs ld.lld for SimpleOS userland)

## Summary

No C hello can be linked for SimpleOS on i686, arm32 or riscv32, with either
ld.lld or the Simple linker, because the userland inputs do not exist. This is
not a linker bug. The kernel side is ahead of the userland side: all three
arches already have filesystem-launch spawn code.

## What exists

| piece | i686 (x86_32) | arm32 | riscv32 |
|---|---|---|---|
| kernel fs-exec spawn | `src/os/kernel/loader/x86_32_fs_exec_spawn.spl` | `arm32_fs_exec_spawn.spl` | `riscv32_fs_exec_spawn.spl` |
| kernel user entry | `arch/x86_32/user_entry.spl` | `arch/arm32/user_entry.spl` | `arch/riscv32/user_entry_v1.spl` |
| syscall ABI in kernel | `int 0x80` (`arch/x86_32/early_syscall.spl`) | `svc`, id 60 = write (`loader/arm32_real_exec_payload.spl`) | `ecall`, 60 = write, 0 = exit (`loader/rv32_real_exec_payload.spl`) |
| compiler lld path | none | none | `link_simpleos_riscv32` (`simpleos_native_linkers.spl:647`); it links against the KERNEL script `arch/riscv32/linker.ld` with a UART stub, so it is a bare-metal link, not a userland one |

## Exactly what is missing (per cell)

1. **crt0**: `src/os/libc/` has only `simpleos_crt0.S` (x86_64) and
   `simpleos_crt0_aarch64.S`. No `simpleos_crt0_i686.S`, `simpleos_crt0_arm32.S`
   or `simpleos_crt0_riscv32.S`.
2. **Syscall stub**: only `simpleos_syscall.S` (x86_64), `_aarch64.S` and
   `_riscv64.S` exist. There is no 32-bit stub for `int 0x80`, `svc` or rv32 `ecall`.
3. **Sysroot script**: only `scripts/os/simpleos-sysroot-aarch64.shs` and
   `-riscv64.shs` exist (x86_64 is built into `build/os/sysroot`). Nothing builds
   `build/os/sysroot-{i686,arm32,riscv32}/` (`lib/crt0.o`, `libsimpleos_c.a`,
   `share/simpleos/simpleos.ld`).
4. **User linker script**: no userland `simpleos.ld` for any 32-bit arch. Its load
   address has to match what the kernel spawn maps.
5. **lld argv**: `simpleos_user_link_args_for_arch` (`simpleos_native_symbols.spl`)
   has no 32-bit branch (`-m elf_i386` / `armelf` / `elf32lriscv --no-relax`).
6. **Simple linker**: `internal_link_simpleos`
   (`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:1387`)
   accepts x86_64, aarch64 and riscv64 only, so 32-bit SimpleOS targets are rejected
   before `elf_boot_link`. Whether `elf_boot_link` itself handles ELF32 relocations
   for i386 and rv32 is unproven. arm32 has a separate `elf/arm32_raw_link.spl`
   path (EFI lane, PR #10239), not wired for SimpleOS userland.
7. **libc portability**: the `src/os/libc/*.c` sources have not been built for an
   ILP32 target, so `long`/pointer-size assumptions are unverified.

## Order to unblock

Items 1-4 per arch, then 5 (the lld reference), then 6 (Simple linker vs readelf of
lld), the same as the 64-bit cells (`simpleos_user_elf_boot_blocked_aarch64_riscv64_2026-11-19.md`).

## Repro

```sh
ls src/os/libc | grep -E 'crt0|syscall'      # no i686/arm32/riscv32 files
ls scripts/os | grep sysroot                 # aarch64 and riscv64 only
```

## Update 2026-11-19: i686 built

- crt0 `src/os/libc/simpleos_crt0_i686.S` is 7 instructions: it hands the entry stack to
  `__simpleos_start32` in `src/os/libc/simpleos_crt0_start32.c`. That C file does the stack
  admission (argc <= 64, argv/envp bounds, exit 127), bss, environ, `rt_set_args`, startup
  admission (exit 125), init_array, module inits, main and exit. It is shared by all three
  32-bit arches.
- Syscall stub `src/os/libc/simpleos_syscall_i686.S`: the int64 cdecl args' low words go to
  eax/ebx/ecx/edx/esi/edi, then `int $0x80`, then `cltd`. This is the kernel's
  `trap_model.spl` map.
- Sysroot: `sh scripts/os/simpleos-sysroot-32.shs i686` builds `build/os/sysroot-i686`. The
  whole libc compiles for ILP32 with no errors (item 7). The Simple C runtime is not
  cross-built yet.
- Linker script: ENTRY-only. The image base 0x400000 comes from `--image-base` and is inside
  the x86_32 window (< 0xC0000000).
- lld args: the `i686` branch in `simpleos_user_link_args_for_arch` adds
  `-m elf_i386 --image-base=0x400000 --build-id=sha1` and crt0.
- Simple linker: `internal_link_simpleos` admits i686 and routes it to the static ELF32
  engine (`elf_link_with_operations`), not `elf_boot_link`. Item 6's ELF32 question was
  routed around rather than answered. SECTIONS scripts are rejected on 32-bit targets.
- A C hello links with both linkers. Remaining divergences: PT_PHDR, `__bss_start`, a stale
  UND `__udivdi3` and `.comment`. They are tracked in
  `elf_static_exec_missing_pt_phdr_and_x86_trap_fill_2026-11-19.md`.
- Not booted: there is no i686 user-mode filesystem-launch boot lane yet.

riscv32 and arm32 remain open.

## Update 2026-11-19: riscv32 built

- crt0 `simpleos_crt0_riscv32.S` is 4 instructions into the shared `__simpleos_start32`.
  The syscall stub `simpleos_syscall_riscv32.S` moves the ILP32 int64 register pairs and
  stack words into the kernel's a7 = id, a0..a4 = args map (`riscv32/user_entry_v1.spl`),
  issues `ecall`, then sign-widens into a1.
- Sysroot: `sh scripts/os/simpleos-sysroot-32.shs riscv32` uses
  `-march=rv32imac -mabi=ilp32 -mno-relax`. One libc fix was needed:
  `simpleos_softfloat_builtins.c` used `unsigned __int128` for binary128 `long double`, and
  rv32 has binary128 long double but no `__int128`. That path is now also gated on
  `__SIZEOF_INT128__`, so rv32 has no `__extenddftf2` until it gets a 32-bit-word
  implementation.
- lld args: `-m elf32lriscv --no-relax --image-base=0x400000 --build-id=sha1` plus crt0.
- Simple linker: `internal_link_simpleos` admits riscv32 through the static ELF32 engine. A
  C hello links with both linkers: `.text` is 0x274 bytes in both, and RW filesz/memsz is
  4/0x410 in both. The engine bug found here (.sdata merged into .data) is fixed in this PR;
  see `elf_static_riscv_sdata_merged_into_data_gp_wrong_2026-11-19.md`.
- The kernel's own `rv32_real_exec_payload.spl` loads at 0x400000, which confirms the base.

arm32 remains open.
