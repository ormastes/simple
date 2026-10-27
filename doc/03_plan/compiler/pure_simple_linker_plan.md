# Pure-Simple Linker — Full Matrix Plan (2026-10-27)

Goal: the pure-Simple linker (`src/compiler/70.backend/linker/`, "L/") links
**executables, static archives, dynamic libraries and baremetal images** for
**COFF/PE, ELF and Mach-O**, without lld / mold / llvm-ar / link.exe. External
tools remain only as *reference oracles* in specs (clang + lld + llvm-readobj /
llvm-objdump / llvm-ar / llvm-nm; never GCC, never MSVC).

Builds on: `doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md`
(owner map §2, mold phases §5, BootLayoutPlan §9) and
`doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md`. This plan
does not replace those; it adds the **format × kind × arch matrix** and one
acceptance criterion per cell. Cross-compile matrix
(`doc/03_plan/compiler/cross_compile_matrix_plan.md`, cells `<triple> × <kind>`)
links its "pure-Simple linker" column to the AC ids below.

## 1. Audit (2026-10-27, origin/main bf9c7fd3e10)

Pure engine = `coff/*`, `elf/*`, `macho/*`, `boot_layout/*`, `_ElfWriter/*`,
`reloc_engine.spl`, `sym_resolver.spl`, `archive_parser.spl`, `linker_script.spl`.
Shell-out wrappers (not counted) = `mold.spl:15-16,73-78`, `msvc.spl`,
`lld_sffi.spl`, `_LinkerWrapper/{native,shared}_linking.spl`, `link_engine_external.spl`.

| Format | Kind | x86_64 | i686 | aarch64 | arm32 | rv32 | rv64 |
|---|---|---|---|---|---|---|---|
| COFF/PE | exe | done | missing | done | missing | n/a | n/a |
| COFF/PE | dll (+export dir, import lib) | partial | missing | partial | missing | n/a | n/a |
| COFF | static `.lib` writer | missing | missing | missing | missing | n/a | n/a |
| ELF | exe (static / static-PIE / dynamic) | done | missing | done | missing | missing | missing |
| ELF | `.so` output | missing | missing | missing | missing | missing | missing |
| ELF | `.a` writer | missing | missing | missing | missing | missing | missing |
| ELF | baremetal (script, MEMORY, LMA, PT_LOAD) | done | missing | done | partial | missing | missing |
| ELF | flat `.bin` + entry/vector placement | missing | missing | missing | done (flat) | missing | missing |
| Mach-O | exe | missing? | n/a | partial | n/a | n/a | n/a |
| Mach-O | dylib output | missing | n/a | missing | n/a | n/a | n/a |
| Mach-O | static archive | (shared ar writer) | n/a | (shared) | n/a | n/a | n/a |

Evidence:
- COFF exe: `coff/coff_link.spl:1330-1397` (AMD64+ARM64, REF/ICF/FORCE:MULTIPLE),
  `coff/pe_image_writer.spl`, `coff/pe_import_builder.spl`, `coff/pe_base_relocation.spl`.
  Hosted hello world links (PRs #4951/#4952/#4958).
- COFF dll partial: `coff/pe_export_builder.spl` exists; no `IMAGE_FILE_DLL`
  characteristic, no DllMain entry policy, no import-lib emission.
- i686: no `IMAGE_REL_I386_*` / `R_386_*` anywhere.
- ELF exe: `elf/elf_static_link.spl:6-9` (modes), `:178-180` accepts only
  `EM_X86_64`/`EM_AARCH64`; `elf/synthetic_sections.spl` (PLT/GOT),
  `elf/elf_exec_writer.spl:263` (PT_DYNAMIC), `elf/tls_relax.spl`.
- `.so`: `elf/shared_object.spl` is a reader only.
- Archives: readers only — `archive_parser.spl`, `coff/archive_closure.spl`,
  `elf/archive_closure.spl`. No writer in the repo.
- Baremetal: `linker_script.spl:326-639` (MEMORY), `boot_layout/boot_layout_plan.spl:420`,
  `elf/elf_boot_link.spl:123-125` (x86_64/aarch64 only), `:651` region overflow,
  `:880` PT_LOAD overlap; `elf/arm32_raw_link.spl:197` flat ARM32. No vector-table placement.
- RISC-V: formulas in `reloc_engine.spl` only; helpers `elf/riscv_{align,attributes,link_support}.spl`.
- Mach-O: `macho/macho_static_link.spl:1-2` (freestanding arm64 MH_EXECUTE),
  `macho/hosted_link.spl` (fixups, signature, export trie), `macho/relocations.spl`
  ARM64 only; `macho/dylib.spl` reads provider metadata only.
- mold stages: string merge exact-only (`elf/merge_strings.spl`), section GC
  (`elf/section_gc.spl`, `elf/eh_frame_gc.spl`), streaming (`elf/stream_*.spl`),
  ICF COFF-only. **Parallel resolve and concurrent write: missing** (`max_workers`
  exists only as a wire field, `linker_pack_wire.spl:149`).
- llvm-ar: no live caller found in `src/compiler`/`scripts` (candidate path only,
  `backend/llvm_capability.spl:220`). AC-AR-4 must census the Rust seed
  (`src/compiler_rust`) and build scripts before claiming replacement.
- Specs: no COFF/PE/ELF/Mach-O link specs under `test/unit/compiler/linker/` or
  `L/test/`.

## 2. MDSOC layout (feature × layer)

Features (dimension 1): `archive`, `coff`, `elf`, `macho`, `boot` (baremetal).
Layers (dimension 2), mold-ordered:

| Layer | Concern | Shared owner | Per-format part |
|---|---|---|---|
| R read | parse objects/archives | `archive_parser`, `elf_parser`, `coff/coff_object`, `macho_parser` | — |
| S resolve | symbols, archive fixpoint, COMDAT | `sym_resolver` (+ `smf_link_profile` per design D3) | weak/COMDAT rules |
| M merge | section merge, string merge, GC, ICF | `elf/merge_strings` generalised to `merge/` | section-name maps |
| Y synth | GOT/PLT/IAT/dynamic/export/stub tables | — | `coff/pe_*_builder`, `elf/synthetic_sections`, `macho/` |
| P place | layout, segments, MEMORY regions | `boot_layout/` | PHDR / PE section align / LC_SEGMENT |
| X reloc | values (one oracle, design D4) + field encoders | `reloc_engine` | per-arch encoders |
| W write | image bytes, flat bin, archive bytes | chunked writer | `pe_image_writer`, `elf_exec_writer`, macho writer, `archive_writer` |

Interface exposure: each feature exports exactly one entry
(`link_coff(req)`, `link_elf(req)`, `link_macho(req)`, `link_boot(req)`,
`archive_write(members, kind)`) taking a plain `LinkRequestV1` projection and
returning `NativeLinkResult` + receipt. Helpers stay `_`-prefixed / unexported.
No inheritance; per-arch behaviour is a trait (`RelocEncoder`, `ArchProfile`)
with one impl per arch. Generics `<>`. No `Any` outside `unsafe:`.

## 3. mold-style pipeline (parallel) — AC-PAR-*

| Stage | Parallel unit | AC |
|---|---|---|
| read | one job per input file / archive member | AC-PAR-1: inputs parsed by N workers, output byte-identical to N=1 |
| resolve | sharded symbol table (hash shard → worker), deterministic tie-break by input order | AC-PAR-2: same winners as serial on fixture set with dup/weak/COMDAT |
| merge strings | per-section fragment hashing, shard-merged | AC-PAR-3: tail/suffix merge of `SHF_MERGE|SHF_STRINGS` (beyond exact dedup) |
| layout | serial (cheap) | — |
| write + reloc | one job per output chunk, disjoint ranges | AC-PAR-4: concurrent chunk write, output byte-identical to serial |
| ICF (later) | per-section hash rounds | AC-PAR-5: ELF ICF (`--icf=safe`) after G2 |

Determinism is the gate: every AC-PAR is "byte-identical to N=1". The receipt
names `max_workers`; until a SOSIX worker pool exists, N=1 and the receipt says so.

## 4. Acceptance criteria per cell

Spec rule (all ACs): modern SSpec, `@req AC-*` tag. Fixtures are objects built
by the Simple compiler or clang (`--target=<triple>`), linked by the pure linker,
then checked by (a) validity — `llvm-readobj` / `llvm-objdump` parse with no
warnings; (b) equivalence to `ld.lld` / `lld-link` / `ld64.lld` output
(symbol addresses relative to section, relocated bytes, import/export tables)
where meaningful; (c) run where runnable. A row that cannot run is reported
**BLOCKED: <reason>**, never `skip()`.

### Wave 1 — COFF/PE (current host: Windows x86_64)
- **AC-AR-1** shared ar writer (`archive_writer.spl`): GNU/SysV layout, `/` symbol
  index, `//` long names, even padding, deterministic (mtime/uid/gid 0). Round-trips
  through `archive_parser`; `llvm-ar t` and `llvm-nm --print-armap` agree.
- **AC-AR-2** COFF `.lib`: archive of COFF objects consumed by `lld-link` and by
  the pure COFF linker (closure resolves members).
- **AC-AR-3** BSD/Darwin variant (`__.SYMDEF`) for Mach-O static libs.
- **AC-AR-4** build switch: our build's archive step calls `archive_write`; census
  (seed + scripts) shows zero llvm-ar invocations on the default lane.
- **AC-COFF-EXE-X64** (done; spec owed): hello world links, runs, exit 0, output equal.
- **AC-COFF-EXE-A64**: aarch64 PE validates; equivalence vs lld-link; run BLOCKED
  (no arm64 Windows host) unless one is available.
- **AC-COFF-EXE-I686**: `IMAGE_REL_I386_{DIR32,DIR32NB,REL32,SECTION,SECREL}`
  encoders, PE32 (not PE32+) optional header, `_` symbol decoration; i686 hello
  runs under WoW64 locally.
- **AC-COFF-DLL-X64**: `/DLL` sets `IMAGE_FILE_DLL`, export directory from
  `/EXPORT` + `.drectve`, base relocs mandatory, import lib (`.lib`, short import
  members) emitted; an exe linked against it loads and calls an export.
- **AC-COFF-DLL-A64**, **AC-COFF-DLL-I686**: same, validity + equivalence; run per host.
- **AC-COFF-ARM32**: BLOCKED by policy (Windows ARM32 retired) — stays a visible row.

### Wave 2 — ELF (riscv first)
- **AC-ELF-RV64-BOOT**: `elf_boot_link` accepts `EM_RISCV` (ELFCLASS64), paired
  `PCREL_HI20/LO12_{I,S}`, `HI20/LO12`, `CALL(_PLT)`, `BRANCH`, `JAL`, `RVC_*`,
  `RELAX` handled conservatively (no relax) or with `riscv_align`; linker script
  MEMORY/ENTRY honoured; `.text.init` at reset vector. Runs under QEMU `virt` with
  **OpenSBI real firmware** (`-bios` OpenSBI, payload at 0x80200000) printing via
  SBI console; board path per `.claude/rules/board-runnable.md` documented
  (board identity + boot path), board run BLOCKED until hardware is named.
- **AC-ELF-RV32-BOOT**: same for ELFCLASS32 / rv32imac, QEMU `virt` rv32.
- **AC-ELF-BIN**: flat `.bin` output from PT_LOAD (LMA-ordered, gap-filled),
  entry at image base, vector table section placed at the script's `KEEP(*(.vectors))`
  address — for rv32/rv64/aarch64/arm32; bytes equal `llvm-objcopy -O binary` of
  the lld image.
- **AC-ELF-BOOT-A64**, **AC-ELF-BOOT-ARM32** (ELF output, not just flat): QEMU
  real-firmware lanes per board-runnable rule.
- **AC-ELF-EXE-RV64**: static + static-PIE hosted exe; runs under
  `qemu-riscv64` user mode or the Linux riscv64 QEMU lane.
- **AC-ELF-EXE-I686**, **AC-ELF-EXE-ARM32**, **AC-ELF-EXE-RV32**: R_386 / R_ARM
  encoders; validity + lld equivalence; run BLOCKED until a host/emulator exists.
- **AC-ELF-SO-{X64,A64,RV64,I686,ARM32,RV32}**: ET_DYN, `.dynsym`/`.dynstr`/`.hash`
  + `.gnu.hash`, `DT_SONAME`, PLT/GOT for preemptible symbols, `R_*_RELATIVE` /
  `GLOB_DAT` / `JUMP_SLOT`; a dynamic exe linked against it runs (x64 Linux lane;
  FreeBSD and SimpleOS lanes listed per cross matrix).
- **AC-ELF-AR**: `.a` from ELF objects via AC-AR-1; lld consumes it.

### Wave 3 — Mach-O
- **AC-MACHO-EXE-A64**: hosted arm64 exe (dyld, LC_MAIN, chained fixups, ad-hoc
  signature) validates with `llvm-objdump --macho`; run BLOCKED without a macOS host.
- **AC-MACHO-EXE-X64**: `X86_64_RELOC_*` encoders; validity + ld64.lld equivalence.
- **AC-MACHO-DYLIB-{A64,X64}**: MH_DYLIB, LC_ID_DYLIB, export trie, install name.
- **AC-MACHO-AR**: static lib via AC-AR-3.

### Cross-cutting
- **AC-PAR-1..5** (§3).
- **AC-GATE**: `mold_is_pure_simple_linker_complete()` (design D7) reflects this
  matrix; each done cell flips one `mold_compatibility_features` row.

## 5. PR slicing (small, parallelisable)

| PR | Closes | Depends | Parallel with |
|---|---|---|---|
| P1 archive writer + spec | AC-AR-1, AC-ELF-AR, AC-AR-2 | — | P2, P4 |
| P2 COFF DLL flag + export + import lib | AC-COFF-DLL-X64 | — | P1, P4 |
| P3 COFF i686 encoders + PE32 | AC-COFF-EXE-I686, -DLL-I686 | P2 for dll | P4 |
| P4 ELF riscv64 boot link | AC-ELF-RV64-BOOT | QEMU+OpenSBI for run row | P1-P3 |
| P5 flat bin + vector placement | AC-ELF-BIN | P4 | P6 |
| P6 riscv32 boot | AC-ELF-RV32-BOOT | P4 | P5 |
| P7 ELF `.so` writer x64/a64 | AC-ELF-SO-X64/A64 | — | P5/P6 |
| P8 ELF rv64 exe + `.so` | AC-ELF-EXE-RV64, -SO-RV64 | P4, P7 | — |
| P9 i686/arm32 ELF encoders | remaining ELF cells | P7 | P10 |
| P10 archive switch in build | AC-AR-4 | P1 | P9 |
| P11 Mach-O x64 relocs + dylib | wave 3 | P1 (AC-AR-3) | — |
| P12 parallel stages | AC-PAR-1..4 | P7 | — |
| P13 ELF ICF | AC-PAR-5 | P12 | — |
| P14 specs-owed for done cells | AC-COFF-EXE-X64/A64, ELF x64/a64 exe+boot | — | any |

Each PR: Haiku worker implements in its own worktree; Opus reviews and
completes; Fable reviews before landing; land via `work/*` PR per `.claude/rules/vcs.md`.

## 6. Blockers (visible, not skipped)

- Disk: C: at 100 % (≈200 MB free) on 2026-10-27 — no worker worktrees or spec
  runs until space is freed.
- QEMU + OpenSBI rv run rows: BLOCKED, owner "other-host lane" — QEMU on the
  Windows host is postponed by user directive (removed; disk full). Validity and
  lld-equivalence rows still run here; hosted-exe run rows for rv/i686-Linux/arm32
  are likewise BLOCKED on this host.
- No macOS / arm64-Windows / physical board host: run rows BLOCKED with reason.
