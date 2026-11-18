# Static ELF engine: no PT_PHDR on static executables; x86 .text padding is 0x00, not 0xCC

- **Status:** open
- **Date:** 2026-11-19
- **Found by:** ssos lane, SimpleOS i686 user link compared with ld.lld 18.1.3

## Symptom

Same inputs (`test/fixtures/linker/elf/simpleos32/`), `ld.lld -m elf_i386 -static
--build-id=sha1 --image-base=0x400000` versus the Simple linker
(`link_simpleos_internal`, target `simpleos-i686`, which runs `elf_link_with_operations`
in static-exec mode):

| | ld.lld | Simple linker |
|---|---|---|
| program headers | 6 (PHDR, 3x LOAD, GNU_STACK, NOTE) | 5 (no PHDR) |
| `.text` vaddr / entry | 0x401120 | 0x401100 |
| `.data` vaddr | 0x402140 | 0x402120 |
| `.text` gap between `_start` and `main` | `cc cc cc cc cc` | `00 00 00 00 00` |

Everything else matches: LOAD flags and alignment, section order, NOTE size, symbol
sizes, and the code bytes apart from the absolute address of `counter`, which follows
the 0x20 shift.

## Cause

1. `elf_exec_plan_class` (`src/compiler/70.backend/linker/elf/elf_exec_writer.spl:259`)
   emits PT_PHDR only `if has_interp`. ld.lld emits PT_PHDR whenever the headers are
   inside the first PT_LOAD, which the engine always places them in. This holds for
   x86_64 too: `ld.lld -static` of a one-instruction x86_64 object also has PT_PHDR.
   So every static executable the engine writes is 1 phdr short, and every address
   after the headers is shifted.
2. ld.lld fills gaps inside x86 executable sections with `int3` (0xCC). The engine
   fills them with zeros.

## Fix plan

A separate PR, not part of the 32-bit SimpleOS admission:
- Gate PT_PHDR on "headers are loaded" instead of `.interp`.
- Use 0xCC as the gap fill for SHF_EXECINSTR sections on I386/X86_64.
- Regenerate the affected oracles from ld.lld (the 19 static-engine specs under
  `test/01_unit/compiler/backend/linker/`). Do not change a spec to match the engine.
- Then tighten `simpleos_user32_link_spec.spl` to lld's exact 0x401120 / 0x402140.

## Same comparison, real C hello (sysroot-i686, 2026-11-19)

`build/os/sysroot-i686` crt0 + `hello32.c` + `libsimpleos_all.a`: `.text` is 0x28a bytes in
both outputs and the LOAD flags match. On top of the PT_PHDR shift, the engine:

3. does not define ld.lld's reserved `__bss_start` (it stays a weak UND, 0). Both links leave
   `__bss_end` undefined, so `__simpleos_start32` skips its bss loop either way and the kernel's
   memsz zero-fill clears .bss. No runtime effect today, still a divergence.
4. keeps `__udivdi3` as a GLOBAL UND symtab entry. ld.lld has no such entry: the only
   reference sits in a section that `--gc-sections` drops. No live relocation uses it,
   so it is symtab noise, but a static executable should not list undefined globals.
5. drops `.comment` (ld.lld keeps the merged one).

## Update 2026-11-19: arm32

6. **`.ARM.exidx` / PT_ARM_EXIDX dropped.** ld.lld keeps `.ARM.exidx` (SHT_ARM_EXIDX, `AL`
   linked to `.text`) and emits a PT_ARM_EXIDX program header. The static engine writes
   neither, so a C++/unwinding arm32 user program has no unwind index. A C hello is not
   affected. `simpleos_user32_link_spec` carries a ponytail note at the spot where the
   assertion would go.
7. **`.ARM.attributes` dropped** (non-alloc SHT_ARM_ATTRIBUTES); lld keeps it.

## Fix 1 (PT_PHDR): verification-pending

`elf_exec_writer.spl` now always emits PT_PHDR first, as ld.lld does. Probed with ld.lld
18 on x86_64 and aarch64, with no script and with an ENTRY-only script: every static
executable has PT_PHDR. Before this fix it was gated on `has_interp`. The repro is
`simpleos_user32_link_spec`, which asserts PT_PHDR at 0x400034 and the exact lld i686
`.text` vaddr 0x401120. Exact riscv32/arm32 vaddrs wait on fixes 4/5 (the
PT_RISCV_ATTRIBUTES and PT_ARM_EXIDX headers). The ELF regression set shows the same
pass/fail counts as release/1.0.0 (elf_dynamic_link 0/8, elf_exec_writer 19/32,
elf_x64_dynamic 29/32, elf_gnu_hash 4/6, elf_symtab 6/7 and elf_archive_closure 8/9 were
already failing). Every other ELF spec is green.
