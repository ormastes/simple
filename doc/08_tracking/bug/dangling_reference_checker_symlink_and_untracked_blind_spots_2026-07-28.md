# check-dangling-references: two false-positive classes — symlinked source trees and untracked providers

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
