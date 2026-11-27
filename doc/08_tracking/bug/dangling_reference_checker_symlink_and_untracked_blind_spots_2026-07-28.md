# check-dangling-references: two false-positive classes — symlinked source trees and untracked providers
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-28 · **Status:** open · **Class:** checker defect (false positives)
**Found:** triage of `scripts/check/check-dangling-references.shs` findings scoped
to `src/app/{cli,dashboard}`. 2 of the 25 findings in that scope are not real
dangling references.

## Root cause

`scripts/check/check-dangling-references.shs:103` builds its entire index from

```sh
git ls-files -- 'src/*.spl' | grep -v '^src/compiler_rust/vendor/' | grep -v '^src/runtime/vendor/'
```

`git ls-files` does not descend through symlinks and does not list untracked
files. Any module whose provider is reached one of those two ways is invisible
to the index, so every import of it is reported as declared in no src file.

## Class 1 — provider behind a symlinked directory

```
src/app/cli/_CliMain/main_and_help.spl:31: SYMBOL: imported name `t32_cli_main` is declared in no src file
```

`src/app/t32_cli` is a **symlink**, tracked as mode `120000`:

```
$ git ls-files -s src/app/t32_cli
120000 08e4aef9f63dcf3815d39b7d9ce4642c4772c5d6 0  src/app/t32_cli
$ readlink src/app/t32_cli
../../examples/10_tooling/trace32_tools/t32_cli
```

`t32_cli_main` is genuinely declared, and genuinely tracked — just outside
`src/`:

```
src/app/t32_cli/mod.spl:25: pub fn t32_cli_main(args: [text]) -> i32:
```

(real path `examples/10_tooling/trace32_tools/t32_cli/mod.spl`). `git ls-files
-- 'src/*.spl'` returns the single symlink entry `src/app/t32_cli`, never the 14
`.spl` files behind it, so none of them enter the index.

This repo uses symlinked source trees deliberately (the checker's own header
comment calls out `src/compiler/hir -> 20.hir` etc.), so this is a systematic
gap, not a one-off. Suggested fix: feed the index from a symlink-following
`find` over the tracked directory set, or explicitly resolve tracked `120000`
entries that point at directories and index the `.spl` files under each target.

## Class 2 — provider exists but is untracked

```
src/app/cli/query_lint.spl:19: MODULE: `use compiler.semantics.lint.primitive_types` -- no src file provides this module
```

The provider is present in the working copy and declares the imported symbol:

```
src/compiler/35.semantics/lint/primitive_types.spl   (declares is_bare_primitive_name)
```

but `git status --porcelain` shows it as `??` (untracked), alongside a sibling
`?? src/compiler/35.semantics/lint/leading_operator.spl` and four modified
`lint/` files — i.e. an in-flight parallel session that has not committed yet.

The checker already indexes the **working copy** of tracked files (deliberately,
so a locally deleted file stops providing definitions). Restricting the *file
set* to tracked paths while reading *content* from the working copy is
inconsistent in this direction: a working-copy file that is new gets no vote.

This particular finding is transient and will clear when that session commits.
But the asymmetry will keep producing noise during parallel work, and it
inverts the checker's stated safety posture — a genuinely-missing provider and a
not-yet-committed provider are indistinguishable in the output.

Suggested fix: index tracked-and-present ∪ untracked-and-present `.spl` files
(respecting `.gitignore`), keeping the existing partial-tree refusal guard.

## Impact on the current backlog

Both classes silently inflate the ~357-finding total. Any triage pass that
treats a SYMBOL finding as proof of a missing implementation will chase these.
In the `src/app/{cli,dashboard}` slice they are 2 of 25 (8%); the symlink class
is likely much larger repo-wide, since the numbered compiler tier directories
are all reached through symlinks.


## Resolution 2026-11-25

**Status:** fixed in `scripts/check/check-dangling-references.shs` (branch
`work/p3-dangling-20261125`, base `release/1.0.0`).

### Root cause

The index file set came solely from `git ls-files -- 'src/*.spl'`, which
(a) never descends through tracked symlinks (mode `120000`) and (b) never
lists untracked files — while file *content* was read from the working copy.
Both false-positive classes in this document follow from that one line.

### Fix

Index construction now unions three sources (vendor exclusions unchanged):

1. tracked `src/*.spl` (as before);
2. `git ls-files --others --exclude-standard -- 'src/*.spl'` — untracked,
   non-ignored providers get a vote (class 2);
3. every tracked `120000` entry under `src/`, resolved via `git cat-file -p`
   on its blob (a working-copy `readlink` is impossible where
   `core.symlinks=false`, e.g. Windows) and normalized with
   `realpath -m --relative-to=<physical root>` — `git rev-parse
   --show-toplevel` prints a drive-letter path on Windows that `realpath`
   cannot relate to the cwd, so the physical `pwd -P` form is used. The
   `.spl` files under each in-repo target are indexed (class 1).

Only the **index** is widened: the default scan-target set remains the
tracked src set, so in-flight or out-of-tree files feed definitions but are
never themselves reported on. The partial-tree refusal guard, the
working-copy presence filter, and all fail-closed ERROR paths are unchanged.

### Evidence

Real-repo run (worktree root, `examples/10_tooling` materialized):

- before: `FAIL -- 1326 dangling reference(s) in 19967 file(s)`
- after:  `FAIL -- 1325 dangling reference(s) in 19967 file(s)`
- `diff` of the two finding lists: exactly one line removed —
  `src/app/cli/_CliMain/main_and_help.spl:62: SYMBOL: imported name
  `t32_cli_main` is declared in no src file` — zero findings added; all
  genuine findings remain.

Selftest: extended from 4 to 6 fixtures. Fixture 5 plants a tracked
`120000` index entry (via `git update-index --cacheinfo`, no filesystem
symlink needed) pointing at a directory whose `mod.spl` declares the
imported symbol — red before the fix (MODULE + SYMBOL false positives),
green after. Fixture 6 imports a symbol from an untracked working-copy
provider — red before, green after. `sh -n` clean;
`--selftest` prints `selftest 6/6 fixtures correct` (exit 0), and the
selftest also runs green as part of every normal checker invocation.
