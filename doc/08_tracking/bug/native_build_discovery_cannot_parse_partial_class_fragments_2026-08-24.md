# `native-build` discovery cannot parse partial-class fragment files (2026-08-24)

- Status: OPEN (P2)
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`
- Blocks: building any SimpleOS kernel whose entry closure reaches
  `src/os/kernel/fs/fat32` — which is every x86_64 kernel entry, including
  `nvfs_positioned_entry.spl`, the ONLY entry that calls `boot_fs_sequence()`
  and therefore the only route to a dbfs/nvfs guest mount.

## Symptom

```
$ bin/simple native-build --entry-closure \
    --entry examples/09_embedded/simple_os/arch/x86_64/nvfs_positioned_entry.spl ...
Build failed: failed to parse .../src/os/kernel/fs/_Fat32Filesystem/allocation_and_write.spl
  at 3:1 during discovery: Unexpected token: expected expression, found Indent
```
rc=1, no artifact.

## Cause: the file is a fragment, and it is supposed to be

`src/os/kernel/fs/_Fat32Filesystem/` is a partial-class split. The header lives
in one file and the rest are continuations of its `impl`:

- `filesystem_state.spl:1` `class Fat32Filesystem:`
- `filesystem_state.spl:25` `impl Fat32Filesystem:`
- the other **7** files in the directory open at indent level 1 with
  `fn name(self, ...)` and no `impl` header of their own.

`allocation_and_write.spl` is one of those seven: line 1 is a comment, line 2 is
`use os.kernel.fs.fat32.*`, line 3 is blank, line 4 is `    fn _write_fat_entry(self, ...)`.
Parsed standalone that is exactly the reported error — an indented block with
nothing to attach to.

So the file is not malformed. **`--entry-closure` discovery parses each source
file in isolation and does not apply the `_ClassName/` partial-class context
that the ordinary compile path applies.** Four such fragment files exist under
`src/os` by the same convention, so this is a pattern, not a one-off.

## Why it matters beyond this lane

This is the second independent defect blocking a SimpleOS kernel build from this
tree (the first is
`doc/08_tracking/bug/seed_parser_multiline_or_chain_context_dependent_2026-08-24.md`).
Together they mean no kernel ELF can be produced here at all, which is why the
dbfs and nvfs QEMU lanes have no transcript. Note this is NOT the admitted-compiler
policy: that policy (`os_build_run.spl:432`, which rejects any binary whose
`--version` says `bootstrap seed only`) blocks `bin/simple os build`. This defect
blocks the lower-level `native-build` path too, so it is a separate wall.

## Fix order

1. Make `--entry-closure` discovery resolve `_ClassName/` partial-class
   directories the way the ordinary compile path does, rather than parsing each
   file standalone.
2. Re-attempt the `nvfs_positioned_entry.spl` build; it is the only entry that
   reaches `boot_fs_sequence()`.
