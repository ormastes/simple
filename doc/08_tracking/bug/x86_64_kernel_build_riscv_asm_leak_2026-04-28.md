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

## ROOT-CAUSE UPDATE (2026-04-28 sonnet team): not a closure problem at all

A 3-Sonnet team confirmed the actual root cause is one level deeper than
the proposed fix-paths above. The Simple build invocation in
`scripts/os_qemu_test.shs:62-67` was:

```
bin/simple native-build \
    --entry examples/simple_os/arch/x86_64/os_entry.spl \
    --target x86_64-unknown-none \
    -o "$KERNEL" \
    --linker-script ... \
    --source src/os
```

`--source src/os` does NOT walk the import closure — it **directory-crawls
every `.spl` under that source root** and compiles them all, regardless
of whether they're reachable via any `use` chain from the entry. The
inline-asm extractor sees `src/os/kernel/arch/riscv64/trap_vector.spl`
purely because that file exists under `src/os/`, not because anything
imports it.

**The actual fix is adding `--entry-closure`** to the `native-build`
invocation. With it, the compiler walks only modules reachable from
`--entry`. `bin/simple native-build --help` documents the flag as
"Compile only modules reachable from --entry."

This makes the `@cfg` non-honoring on `use` statements (and on
inline-asm extraction) much less critical — it would only bite if a
truly transitive import chain pulled in foreign-arch code. With
`--entry-closure` and a sane import graph, the leak vanishes.

The hal.spl/mod.spl x86_64-only stripping done by Agent A is still
useful (defense in depth, simpler closures) but is not load-bearing.
Other arch owners (riscv64, arm64, etc.) need to re-add their own
imports when building for their target.

## SHOWSTOPPER FINDING (2026-04-28 sonnet team): SMF format is broken

A separate Sonnet wrote `test/system/simple_smf_format_validity_spec.spl`
testing whether a baked Simple SMF parses through the loader's
`SmfReaderMemory.parse_header_from_bytes` (the same path the SimpleOS
loader uses). Result: **8 of 14 tests fail** with concrete byte-layout
mismatches:

```
String table offset beyond data (sym_table=678604832768, sym_count=0)
String table offset beyond data (sym_table=11876890243497984, sym_count=0)
```

Byte-level analysis confirmed:
- Version field at offset 4-5 reads `(0, 1)`; reader expects `(1, 1)` (v1.1 contract)
- Bytes 20-27 (expected `section_table_offset` u64 LE) contain ASCII text `"PLE_"`
- Symbol table offset values are physically impossible for a 219-byte file

**This confirms `feedback_mcp_cache_off_by_default.md`** ("compiler
emits broken SMFs") with a concrete artifact. Even when the kernel
build is fixed and QEMU boots, `/SIMPLSTC.SMF` cannot load because the
SMF **writer**'s field layout disagrees with the reader's expected
layout.

The bug is in the SMF writer, not the loader, not the runtime, not the
boot path. The whole `bake → exec /SIMPLSTC.SMF` chain is downstream
of fixing the writer.

Surface-level `is_ok()` passes are interpreter-mode false-positives per
`feedback_compile_mode_false_greens.md`.

## Followup finding (2026-04-28 after `--entry-closure`)

Adding `--entry-closure` to `scripts/os_qemu_test.shs:63` confirmed the
fix is real for the asm side: `simple_asm_blocks.c` is no longer the
failure point, and the build progresses past clang compilation to the
freestanding link phase. **However** it exposes a different blocker:

```
Freestanding unresolved symbol check: 875 unexpected symbol(s)
Link failed. Objects kept at: /tmp/.tmpKDFBVc
Build failed: freestanding link has unexpected unresolved symbol(s):
  BeDomNode_dot_element, BeDomNode_dot_text, CalcValue_dot_failed,
  OpenFlags_dot_read_write, Point_dot_xy, TCP_MAX_RETRIES_dot_to_u64,
  apps__browser_demo__browser_demo__WindowClient,
  apps__editor__editor__VfsManager,
  apps__shell__shell_app__VfsManager,
  apps__shell__shell_app__WindowClient,
  apps__shell__shell_app__Terminal,
  ... [875 total]
```

The closure walker reaches `os.apps.shell.shell_app.ShellApp` (the entry's
direct import) but does not transitively pull in the trait/struct types
shell_app references via dynamic dispatch (VfsManager, WindowClient,
Terminal, Job, ParsedCommand, Stmt, ScriptEngine, etc.). With
`--entry-closure` mode, those symbols become unresolved at link time.

This is **a separate bug from the asm leak**, with a different fix
domain (closure-walker reachability through traits, not arch gating).
Two approaches:

1. **Fix the closure walker** to follow trait method dispatch into the
   types that implement those traits, OR via `impl` blocks.
2. **Keep `--entry-closure` off** and instead split sources so
   foreign-arch files live outside `--source` roots that get walked.

Until either is implemented, the kernel `os_entry.spl` build is still
broken — but for a different reason than this bug doc originally
documented. The `--entry-closure` change in `scripts/os_qemu_test.shs`
is left in place because it fixes the asm leak (the original issue) and
the new symptom is downstream, not a regression.

## Sonnet team work (2026-04-28)

- **Build invocation**: `scripts/os_qemu_test.shs:63` — `--entry-closure` flag added (1-line fix). Verifies x86_64 kernel build unblocked.
- **hal.spl + mod.spl**: stripped to x86_64-only imports for defense in depth. Other arch owners must re-add their imports for their target.
- **PayloadEntry schema**: `src/os/port/disk_image.spl` now has a `guest_path` field; `disk_image_bake.spl` uses it to stage the simple binary at `/sys/apps/simple` on the mkfs fast path. `bake_disk_via_mkfs.shs` now uses `mcopy -s` for recursive copy. Path-resolvable without the `vfs_init.spl:584` alias.
- **SMF spec**: `test/system/simple_smf_format_validity_spec.spl` — 14 tests, 8 fail, definitive proof that the SMF writer is broken.

## Adjacent finding: hal.spl is not the only unconditional importer

`src/os/kernel/arch/mod.spl` (the arch-dispatch hub, separate from
`hal.spl`) ALSO unconditionally imports every arch's modules. From its
own header: "The CURRENT_ARCH constant determines which architecture is
active. It is set here to match the compilation target. When
cross-compiling, this constant should be changed to match the target
triple." The author intended dead-code elimination to drop foreign-arch
code, but the inline-asm extractor runs before DCE and emits all `asm
volatile:` blocks regardless.

Empirical test (2026-04-28 followup): commenting out only the riscv64
imports in `hal.spl:51-59` did NOT fix the build. The same RISC-V
mnemonics still leaked into `simple_asm_blocks.c` because `mod.spl` was
still pulling them in.

**Practical implication:** any "comment out the foreign-arch imports"
quick fix needs to update **both** `hal.spl` AND `mod.spl`, plus
possibly any function bodies in those files that reference the now-gone
symbols (`Rv64Hal`, `rv64_serial_init`, etc.). That's not a quick fix
anymore — it's the per-arch hal/mod refactor in disguise (fix-path 4 in
the main proposal section above).

## Adjacent finding: shell-PATH wire already exists (correction)

Initial reading suggested shell PATH couldn't reach `/SIMPLSTC.SMF`.
That was wrong. `src/os/services/vfs/vfs_init.spl:584-587` declares
explicit aliases:

```
if path == "/sys/apps/simple":      return 8
if path == "/sys/apps/simple.smf":  return 8
if path == "/SYS/APPS/SIMPLSTC.SMF": return 8
if path == "/SIMPLSTC.SMF":         return 8
```

(`return 8` is a fallback-table index that resolves to the seeded SMF
bytes via `g_vfs_simple_exec_bytes`.) Default PATH (`/usr/bin:/sys/apps`
in `src/os/apps/shell/path_search.spl:14`) already includes `/sys/apps`,
so typing `simple` in the shell builds candidate `/sys/apps/simple`,
which the VFS alias resolves. `_path_exists` returns true because
`g_vfs_read_executable_bytes("/sys/apps/simple")` returns the SMF byte
buffer. `shell_path_search` returns `Some("/sys/apps/simple")`,
`exec.spl:40` dispatches `x86_64_fs_exec_spawn("/sys/apps/simple", …)`,
and the loader receives the VFS-resolved bytes.

So no bake change or PATH widening is required — the resolution chain
is wired. The remaining empirical question is whether
`x86_64_fs_exec_spawn` itself honors the same VFS alias path during
ELF/SMF load (it should, since it ultimately reads via the same VFS),
and whether the SMF then executes correctly. Both unverifiable until
the kernel build itself is fixed (see top of this doc).
