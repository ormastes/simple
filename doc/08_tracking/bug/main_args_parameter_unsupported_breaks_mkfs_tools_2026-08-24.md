# `fn main(args: [text])` is unsupported and silently reads uninitialised memory (2026-08-24)

- Status: OPEN (P1 for the silent-garbage half) — call sites migrated, root cause NOT fixed
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`
- Blocked: `scripts/os/mkfs-dbfs.shs` and `scripts/os/mkfs-nvfs.shs`, i.e. the
  ability to format SimpleOS's own filesystems at all

## Symptom

`src/os/port/mkfs_dbfs.spl` and `src/os/port/mkfs_nvfs.spl` both declared
`fn main(args: [text])`. Running either through its wrapper:

```
$ sh scripts/os/mkfs-dbfs.shs build/os/simpleos_dbfs_root.img 65536
error: semantic: function expects argument for parameter 'args', but none was provided
```
rc=1.

## The dangerous half

Reduced to a two-line fixture:

```
fn main(args: [text]):
    print "n={args.len()}"
```

| invocation | result |
|---|---|
| `run m1.spl -- a b` | semantic error, rc≠0 |
| `run m1.spl a b` | semantic error, rc≠0 |
| `run m1.spl` | **rc=0, prints `n=8246223157400007265`** |

The no-argument case does not fail. It runs, and `args.len()` returns
uninitialised memory. A tool written against this signature will not crash — it
will branch on garbage. That is worse than the hard error and is why this is
filed P1 rather than as a missing feature.

## What was changed

Both mkfs entry points now read argv explicitly via
`std.nogc_sync_mut.io_runtime.get_args()`, which works correctly under the
current toolchain (it returns `[script_path, "--", ...user args]`, so a small
`_user_args()` helper drops the script path and the `--` separator). Each
carries a comment pointing here.

Verified after the change:
```
$ sh scripts/os/mkfs-dbfs.shs build/os/simpleos_dbfs_root.img 65536
mkfs.dbfs: wrote build/os/simpleos_dbfs_root.img (65536 sectors)
```
rc=0, 33554432-byte image produced.

## Not migrated

`/usr/bin/grep -rln 'fn main(args' src/` reports **11** files. Only the two mkfs
tools were migrated here, because only those were on this lane's critical path.
The other nine are still exposed to the silent-garbage behaviour above and
should be swept once the underlying signature is either implemented or rejected
at compile time.

## Fix order

1. Make `fn main(args: [text])` either work or be a hard compile error. It must
   never be a silent read of uninitialised memory.
2. Sweep the remaining 9 declarations.
3. Drop the `_user_args()` helpers if (1) implements the signature.
