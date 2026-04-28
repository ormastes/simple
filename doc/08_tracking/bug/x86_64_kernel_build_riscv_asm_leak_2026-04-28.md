# Bug: x86_64 kernel build leaks RISC-V inline asm into the consolidated C blob

**Filed:** 2026-04-28
**Severity:** Blocker — `bin/simple` x86_64 kernel build broken on `main` HEAD.
**Discovered while:** running Step 1 of `~/.claude/plans/complete-porting-llvm-rust-reactive-cosmos.md`
(boot-time smoke-test of `/SIMPLSTC.SMF`).

## Symptom

`sh scripts/os_qemu_test.shs --tier 1` fails during the clang stage with
20+ errors of the form:

```
/tmp/.tmpXXXXXX/simple_asm_blocks.c:31:10: error: unknown token in expression
   31 |         "ld      a4, 104(a0)\n"
      |          ^
<inline asm>:18:16: note: instantiated into assembly here
   18 | ld      a4, 104(a0)
      |                ^
fatal error: too many errors emitted, stopping now [-ferror-limit=]
```

`ld a4, 104(a0)` is RISC-V (loading from offset 104 of `a0` into `a4`). The
clang invocation is targeting x86_64 — these mnemonics are not valid x86.

## Root cause

`src/os/kernel/arch/riscv64/trap_vector.spl` declares `_rv64_trap_vector`
with an `asm volatile:` block of RISC-V instructions. The function has
`@section(".text.trap")` and `@naked` but **no arch-gate** (e.g. no
`@cfg(target_arch="riscv64")` or equivalent).

The Simple compiler's build closure walks all `.spl` files reachable from
the entry point and consolidates every `asm volatile:` block into a single
generated C file (`simple_asm_blocks.c`). When the entry point is
`examples/simple_os/arch/x86_64/os_entry.spl` and the target triple is
x86_64, the walker still pulls in `arch/riscv64/trap_vector.spl` (likely
via a transitive `mod.spl` re-export or a directory-level glob) and emits
its asm block into the host clang invocation. clang rejects RISC-V
mnemonics and the kernel build fails.

The path itself (`src/os/kernel/arch/riscv64/`) signals arch-specificity,
so either:

1. **The walker should skip `arch/<other-arch>/*` when the target triple
   doesn't match.** Right fix structurally — paths are the source of
   truth for arch ownership.
2. **Each arch-specific `.spl` should declare an explicit arch-gate.**
   More verbose but local; doesn't depend on path conventions.

## Reproduction

```
sh scripts/os_qemu_test.shs --tier 1
# (or the inner cargo/build invocation that produces simple_asm_blocks.c
#  for the x86_64 target — the walker is the same regardless of harness.)
```

Reproduces deterministically on HEAD as of `b233017dd2`.

## Adjacent symptom (already fixed in this session)

While diagnosing this bug we also discovered that
`src/os/services/vfs/nvfs_connector.spl` had been committed in commit
`0515a3d0b7` ("feat(simpleos): harden NVFS connector with Result returns
+ caps + bounds") with un-replaced `/* complex expr */` placeholder
comments and bare-`"` multi-line docstrings. The file was syntactically
invalid and would have blocked the kernel build before reaching the
RISC-V asm leak, but it's restored in this working tree from the
pre-bad-commit version (`0515a3d0b7^`). That fix is uncommitted and
doesn't address this RISC-V issue.

## Impact

- Cannot empirically test whether `/SIMPLSTC.SMF` boots from FAT32 (the
  goal of the `simple-from-FS` plan).
- Cannot run any x86_64 kernel-level integration test on HEAD.
- Anyone who ran `bin/simple build` and reported "tests passed" on x86_64
  recently was either skipping `--tier 1` or running off a different
  branch.

## Empirical findings (2026-04-28 follow-up)

I attempted to apply the file-level `@cfg` arch-gate fix (proposal 1
below). It does not work, for two reasons:

- **The two-arg form `@cfg("target_arch", "riscv64")` is silently
  ignored.** I added it at the top of all 5 RISC-V files
  (`trap_vector.spl`, `cpu.spl`, `context.spl`, `sbi.spl`, `boot.spl`,
  modeled on the precedent at
  `src/lib/nogc_async_mut_noalloc/baremetal/arm/semihost.spl:15-18`).
  Rebuilt; same RISC-V mnemonics still appeared in
  `simple_asm_blocks.c`. The arm/semihost.spl precedent is a no-op for
  inline-asm extraction.
- **The single-arg form `@cfg(riscv64)` (used at function level in
  `src/os/kernel/arch/hal.spl:217-242`) is also evidence that `@cfg`
  doesn't gate `use` statements.** `hal.spl` lines 22-69 import
  x86_64, x86_32, arm64, arm32, riscv64, and riscv32 modules
  unconditionally. When targeting x86_64, the riscv64 imports still
  pull `arch/riscv64/*.spl` into the build closure; the inline-asm
  extractor then emits all those `asm volatile:` blocks into
  `simple_asm_blocks.c` regardless of the body-level `@cfg(riscv64)`
  guards on hal.spl's functions.

The `@cfg` attribute appears to gate something later in the pipeline
(possibly type-check or codegen of the function body), but NOT:

1. Whether the file is included in the build closure
2. Whether `use` statements drag in foreign-arch modules
3. Whether `asm volatile:` blocks are emitted to the consolidated C blob

Until one of these is fixed in the Rust seed compiler, no source-level
attribute fixes the leak.

I reverted my no-op `@cfg` additions to keep the source clean.

## Proposed fixes (in order of locality, REVISED)

1. **(Was proposal 1 — does not work.)** ~~Add an arch-gate to
   `_rv64_trap_vector` etc.~~ Empirically a no-op; left here only so
   future readers don't repeat the experiment.

2. **Make `@cfg` actually gate `use` statements and inline asm
   extraction.** This is a Simple compiler change in
   `src/compiler_rust/` — likely in the import-resolution phase
   (currently `@cfg` is parsed but doesn't filter the closure walker)
   and the inline-asm extraction phase (currently emits all asm blocks
   into `simple_asm_blocks.c`). Right structural fix; non-trivial.

3. **Make the build walker skip `arch/<arch>/` directories whose
   `<arch>` doesn't match the current target triple.** Path-based
   exclusion in the build script or the closure walker. Bypasses the
   `@cfg` machinery entirely. Easier to implement than (2) but only
   covers the common arch case, not generic feature gating.

4. **Refactor `src/os/kernel/arch/hal.spl` to import only the active
   arch's modules.** Either by splitting into per-arch hal files
   (`hal_x86_64.spl`, `hal_riscv64.spl`, etc.) selected by a single
   top-level dispatch import, or by some build-system trick that
   substitutes the right arch at config time. Largest source diff but
   doesn't require compiler changes.

Either path 2, 3, or 4 unblocks the smoke-test work in the
simple-from-FS plan; path 1 does not.

## Adjacent finding: kernel-build-target asymmetry

While diagnosing this bug we observed that `desktop_e2e_entry.spl` builds
cleanly (verified by `build/os/kernel_rebuild2.log` from 2026-04-28
00:28, output `simpleos_desktop_e2e_32.elf`) while `os_entry.spl` does
NOT (the cached `simpleos_x86_64.elf` is from Apr 26). Both target
x86_64 — they differ only in their import closures. `desktop_e2e_entry`
imports compositor / framebuffer / desktop-shell modules and **does not**
transitively pull in `os.kernel.arch.hal`, which is the file with the
unconditional multi-arch `use` chain that drags `arch/riscv64/*` into
the build. `os_entry` imports `os.kernel.boot.init_services`, which DOES
transitively pull in `hal.spl`.

**Practical implication:** any new in-OS smoke test that wants to call
`x86_64_fs_exec_spawn(...)` will compile cleanly only if attached to a
build target whose closure does not include `hal.spl`. Today,
`desktop_e2e_entry.spl` is such a target; `os_entry.spl` is not. This is
a workaround, not a fix — `hal.spl` should be refactored per fix-path 4
above so any kernel build target works regardless of where the call is
attached.

## Adjacent finding: /SIMPLSTC.SMF shell-PATH unreachability

`src/os/apps/shell/path_search.spl:14` hardcodes default PATH to
`/usr/bin:/sys/apps`. The Simple compiler is baked as `/SIMPLSTC.SMF`
at the FAT32 root by `src/os/port/disk_image_bake.spl`. Typing
`simple` in the shell calls `shell_path_search("simple")`, which builds
candidate paths `/usr/bin/simple` and `/sys/apps/simple` — neither of
which exists. The `/sys/apps/SIMPLSTC.SMF` alias in
`src/os/services/vfs/vfs_init.spl:586` doesn't match either (different
filename).

The smallest fix is to bake an additional `PayloadEntry` at
`/usr/bin/simple` (or `/sys/apps/simple`) pointing at the same host
file, so the existing PATH search resolves. That's Step 4 of
`~/.claude/plans/complete-porting-llvm-rust-reactive-cosmos.md`. It is
gated on the kernel build being unblocked — without that, no in-OS
test can verify the wire works.
