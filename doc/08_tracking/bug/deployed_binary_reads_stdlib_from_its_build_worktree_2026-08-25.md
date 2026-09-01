# The deployed binary reads `src/lib` from the worktree it was BUILT in, not the tree you are working in (2026-08-25)

**Status:** OPEN. **Severity: HIGH — this silently invalidates stdlib evidence.** Not a GPU bug;
it was found while investigating one, and it is the actual cause of that "GPU bug".

## Symptom

An edit to `src/lib/**` in your working tree has **no effect**, while a byte-identical edit in a
user module works. The binary executes a *different generation* of the same stdlib file, taken
from an unrelated worktree, and says nothing.

Measured on `bin/release/x86_64-unknown-linux-gnu/simple` (60,646,096 bytes, 2026-08-25 06:08),
running from `/mnt/data/worktrees/simple-main`:

```
$ strace -f -e trace=openat -o t.txt bin/simple run q.spl ; grep gpu_runtime t.txt
openat(".../parsefix-iso/src/lib/nogc_sync_mut/gpu_runtime/mod.spl", O_RDONLY) = 4   <-- FOREIGN
openat(".../simple-main/src/lib/nogc_sync_mut/gpu_runtime/mod.spl",   O_RDONLY) = 4
openat(".../parsefix-iso/src/lib/nogc_sync_mut/gpu_runtime/mod.spl",  O_RDONLY) = 4   <-- FOREIGN
openat(".../simple-main/src/std/nogc_sync_mut/gpu_runtime/mod.spl",   O_RDONLY) = 4
```

Both trees are opened — 32 opens under `parsefix-iso`, 40 under `simple-main` — and for this
module the foreign copy is the one whose behaviour is observed. (`src/std` is a symlink to `lib`,
so rows 2 and 4 are the same file; that part is fine and is not the defect.)

The deployed binary was built in `/mnt/data/worktrees/parsefix-iso` and carries **775** strings
naming that path, including the `src/compiler_rust/compiler/../../../src/lib/...` form that the
strace shows being probed:

```
$ strings -a bin/release/x86_64-unknown-linux-gnu/simple | grep -c parsefix-iso
775
```

## Why it is worse than a stale binary

A stale binary is honest: you get old *compiler* behaviour and can date it. This gives you a
current compiler reading **old stdlib source**, mixes two stdlib generations in one process, and
produces results that look like language or dispatch defects. Every symptom is attributed to the
wrong subsystem.

## What it already cost

`doc/08_tracking/bug/std_gpu_package_import_binds_cuda_externs_to_nocuda_stub_2026-08-25.md`
records `use std.gpu.*` reporting 0 devices and compute capability `(0, -3)` on a 2-GPU host, and
concludes the package import binds `rt_cuda_*` to a no-CUDA stub. **That conclusion is wrong.**
`parsefix-iso`'s copy of `gpu_runtime/mod.spl` is the *pre-fix* version that gates on
`rt_torch_cuda_available()`; this host has CUDA but no PyTorch, so it answers false → `gpu_available()`
false → 0 devices → the `-3` sentinel. The fix (plan row 3) is correct and landed; the binary was
reading the tree it was not applied to. See that record's Correction section.

Four hypotheses were tested and refuted before the strace, each costing a full probe cycle —
stale `.smf` shadowing (parked all 8, no change), a `BrowserNavigator.gpu_available` method
colliding by name (renamed, no change), the `torch.sffi` import poisoning the extern (added to a
user module, still correct), and module caching (`rm -rf .simple/cache`, no change). The
discriminator that would have caught it immediately was a sentinel value: editing the file to
return `777` and observing that `777` never appears proves the file is not being read, and says
nothing about which resolution rule is at fault. **Use a sentinel before theorising about
resolution.**

## Reproduce

```bash
# 1. put a sentinel in a stdlib function you can call
sed -i 's/^        0$/        777/' src/lib/nogc_sync_mut/gpu_runtime/mod.spl
# 2. call it -- prints 0, never 777
printf 'use std.gpu_runtime.*\nfn main():\n    print "{gpu_device_count()}"\n' > /tmp/q.spl
bin/simple run /tmp/q.spl
# 3. see who actually answered
strace -f -e trace=openat -o /tmp/t.txt bin/simple run /tmp/q.spl
grep gpu_runtime /tmp/t.txt
```

## Where to look

`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs` (`resolve_module_path`, the
`variants/` overlay search around :763, and the stdlib search below it) and
`interpreter_module/module_loader.rs`. Note the `env!("CARGO_MANIFEST_DIR")` uses in both files
(:1349/:1369/:1401 and :1580/:1612) are inside `#[test]` modules and are **not** the production
path — do not "fix" those and call it done. The production redirection has not been pinned to a
specific line; what is proven is the behaviour, the baked path, and which file wins.

## Suggested guard

The cheap, fail-closed check is a startup-time assertion, not a scan: the binary should resolve
its stdlib root relative to the invoking project (or an explicit env override) and **refuse to
silently prefer a root outside it**. Absent that, a pre-push or deploy-time guard can compare the
deployed binary's baked repo-root strings against the repo it is deployed into and FAIL on
mismatch — a deployed compiler built somewhere else is a defect regardless of which files it
happens to open. Related and already-known: `.claude/memory/nested-git-shadows-stdlib.md` records
the same class reached by a different route (a nested `.git` redirecting stdlib reads), which is
why "strace before trusting stdlib results" is already standing advice.

## Impact on other sessions' evidence

Any measurement of `src/lib/**` behaviour taken with this deployed binary, from any worktree other
than `parsefix-iso`, is **unverified** — it may have exercised either tree. This includes green
results: a spec that passes may be passing against foreign source.
