# native-build rejects an entry file outside the source roots: "missing importing module surface" (2026-08-22)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## 2026-11-10 status — SUPERSEDED (P3 bootstrap lane row 47, work/p3-boot6-20261110)

Fixed in-tree on this lane's base (`4343ce254922`). The exact emitting
condition is gone: `src/compiler/20.hir/hir_lowering/_Items/
module_import_resolution.spl:327-377` (`resolve_import_list`) no longer
treats an absent importing-module surface as a hard error. A no-import
module returns early (`imports.len() == 0`), which covers this record's
three-line out-of-tree hello world verbatim; a with-import module whose own
surface is unregistered (out-of-tree entry, unit fixtures, single-module
embedders) falls back to re-deriving the import item rows from the live
parser import decls (a verbatim flatten of `owner.value.imports` by
construction), preserving semantics exactly. The in-code comment names this
defect family explicitly. Landed via the #7463/#7492/#7545/#7597 merge chain
(all ancestors of this base); the surface-miss diagnostic under
`SIMPLE_BOOTSTRAP_DIAG=1` (`[surface-miss] ... registry_size=...`) is the
fail-loud breadcrumb if it ever resurfaces. Pinned by
`test/01_unit/compiler/hir/standalone_module_no_imports_needs_no_surface_spec.spl`,
`test/01_unit/compiler/common/module_path_naming_spec.spl` (out-of-tree
`entry_main_symbol=false` contract) and
`test/01_unit/compiler/driver/dotted_source_entry_identity_spec.spl` —
seed-smoke results in build/review/p3fix-boot6-20261110.sdn. The
synthetic-root registration this record suggested is unnecessary given the
fallback; no bootstrap-script workaround is needed any more.
