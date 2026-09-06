# native-build rejects an entry file outside the source roots: "missing importing module surface" (2026-08-22)

**Status:** OPEN (tree-side regression, not a seed regression). Workaround in
place for the bootstrap pipeline (hello-world fixtures are written INSIDE the
worktree, `build/tmp/...`).

## Symptom

A three-line hello world at a path outside the worktree (the agent scratchpad,
`.../scratchpad/fp8/gate/hello.spl`) no longer native-builds on tree
`1c8757fb745` / `37bd406e219`:

```
[hir-fatal] source_idx=0 path=<scratchpad>/fp8/gate/hello.spl error_idx=0 text=HIR lowering error in /mnt/data/tmp/claude-1000/-mnt-data-worktrees-simple-main/8d1153fd-22a9-4fab-b37d-eeae6a7f8eac/scratchpad/fp8/gate/hello.spl: missing importing module surface for /mnt/data/tmp/claude-1000/-mnt-data-worktrees-simple-main/8d1153fd-22a9-4fab-b37d-eeae6a7f8eac/scratchpad/fp8/gate/hello.spl
[hir-fatal-count] source_idx=0 path=<scratchpad>/fp8/gate/hello.spl count=1 shown=1
[hir-poisoned] source_idx=0 path=<scratchpad>/fp8/gate/hello.spl module=.mnt.data.tmp.claude_1000....hello
[ERROR] phase 3 FAILED
error: HIR lowering error in <scratchpad>/fp8/gate/hello.spl: missing importing module surface for <scratchpad>/fp8/gate/hello.spl
```

(`simple native-build <scratch>/hello.spl -o <scratch>/hello`, rc=1, 63 s;
full log `scratchpad/fp8/gate/log_hello_native_build.txt`.)

## Control (same tree, same command, two seeds)

| seed | entry location | result |
|---|---|---|
| deployed `simple.deployed-dee19c5` | scratchpad (out of tree) | **rc=1**, 5x "missing importing module surface" |
| candidate `simple.1c8757fb745` | scratchpad (out of tree) | **rc=1**, same text |
| candidate `simple.1c8757fb745` | `build/tmp/gate8/hello.spl` (in tree) | **rc=0**, 24,920-byte binary, prints `hello` |

Both seeds fail identically on the out-of-tree path and the candidate passes
in-tree, so the rejection comes from the pure-Simple driver on this tree (the
module-surface registry that now backs HIR import lowering — `reg_imported`
in `[hir-prof]` — has no entry for a module whose file is not under any
`--source` root / the cwd), not from the Rust seed.

## Why it matters

`bin/simple native-build some/absolute/path.spl` with no `--source` used to
work (that is what `scripts/check/check-stage-binaries-runnable.shs` and
the hello-world deploy gate rely on, both of which write their fixture to a
private temp dir). Any gate that does so now reports a false RED against the
seed.

## Workaround / expected fix

- Workaround: put the entry under the worktree (`build/tmp/<lane>/`) — done in
  `scratchpad/pipe/sanity.sh` and `scratchpad/fp8/gate.sh`.
- Fix: when the entry file is outside every source root, register its surface
  under a synthetic root (its parent directory), as the pre-registry loader
  did, instead of failing the HIR phase.
