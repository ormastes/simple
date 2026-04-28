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

## Proposed fixes (in order of locality)

1. Add an arch-gate to `_rv64_trap_vector` in
   `src/os/kernel/arch/riscv64/trap_vector.spl` (and any sibling files
   under `arch/riscv64/` and `arch/aarch64/`, `arch/arm64/` etc. with
   inline asm).
2. Make the build walker skip `arch/<arch>/` directories whose `<arch>`
   doesn't match the current target triple. Implement once; benefits
   every future arch-specific module.

Either path unblocks the smoke-test work in the simple-from-FS plan.
