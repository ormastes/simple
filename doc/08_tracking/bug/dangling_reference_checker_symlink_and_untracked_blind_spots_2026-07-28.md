# check-dangling-references: two false-positive classes — symlinked source trees and untracked providers

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

---

## SEPARATE DEFECT, FOUND AND FIXED 2026-08-17 — the checker could exit 0 having scanned nothing

The two blind spots above are false-POSITIVE (noise) classes and remain OPEN.
While working this row a third, opposite, and strictly worse defect was found in
the same script: a **vacuous pass**. It is fixed.

### Defect

Both scan passes were pipelines whose exit status was never read:

```sh
xargs -a "$tmp/all.txt"     -d '\n' awk -f "$tmp/index.awk" | sort -u > "$tmp/index.txt"
xargs -a "$tmp/targets.txt" -d '\n' awk -v idx=... -f "$tmp/check.awk" > "$tmp/viol.txt"
```

`awk`'s `fatal:` aborts the entire batch, so every file after the offending one
in that `xargs` batch was **never scanned**. `viol.txt` then came back empty and
the script printed `OK -- no dangling references` and exited **0**. The verdict
carried no count, so a run that scanned zero files was indistinguishable from a
clean one. `sort`'s status is what `$?` held for pass 1 — the exact
"never read rc through a pipe" trap.

Trigger is not hypothetical: one unreadable/vanishing tracked `.spl` is what a
concurrent `jj` checkout produces, and this repo runs ~15 concurrent lanes.

### Reproduction (throwaway git repo, 4 tracked `.spl` files, one real violation)

```
# beta.spl readable
check-dangling-references: FAIL -- 1 dangling reference(s)      rc=1
# chmod 000 beta.spl, same tree, same violation still present
awk: ... fatal: cannot open file `src/lib/beta.spl' for reading: Permission denied
check-dangling-references: OK -- no dangling references         rc=0
```

A genuine dangling reference was masked and the gate went green.

### Fix

`scripts/check/check-dangling-references.shs`:

- pass 1 writes to a file and reads `index_rc=$?` on the **next** line, then
  sorts; nonzero -> ERROR exit 2 (an incomplete definition index makes every
  finding, positive or negative, unsound);
- pass 2 likewise reads `scan_rc=$?` on the next line;
- `check.awk` counts the files it actually opened (`FNR == 1 { scanned++ }`,
  `END { print "#SCANNED\tn" }`, summed across `xargs` batches) and the shell
  requires `scanned == targets_n` and `scanned > 0`;
- verdicts now follow the repo convention and are always the last stdout line:
  `PASS -- <n> file(s) checked, 0 dangling references` (0) /
  `FAIL -- <n> dangling reference(s) in <m> file(s)` (1) /
  `ERROR -- nothing was checked: <why>` (2). `OK` is gone.

### `--selftest` (runs before every scan, fatal)

Three throwaway git repos scanned through the script's own entry point
(`DANGLING_REF_SELFTEST_CHILD=1` stops the recursion):

1. clean tree -> must PASS, exit 0, count > 0;
2. one dangling `self.method()` -> must FAIL, exit 1;
3. fixture 2 **plus one unreadable tracked `.spl`** (incident replay) ->
   must ERROR, exit 2 — this is the fixture that was green before the fix.

Fixture 3 cannot be built as root; that case is reported as ERROR exit 2, never
as a pass.

Mutation-tested: neutering all four non-vacuity guards turns the selftest RED
with `FIXTURE 3 ... got rc=0 out='... PASS -- 0 file(s) checked ...'`.
The four guards are deliberately redundant — disabling any three still catches
the incident (awk dies before `END`, so no `#SCANNED` sentinel is emitted at
all).

### Live confirmation on the real tree

The first full-repo run of the fixed guard returned

```
check-dangling-references: ERROR -- nothing was checked: scan pass opened 14685 of 14691 target file(s)
real-repo rc=2
```

with `scan_rc == 0` — i.e. **no** awk fatal, and the pre-fix script would have
printed a clean-looking verdict. The 6-file gap turned out to be benign: six
tracked `.spl` files under `src/` are 0 bytes (five `src/compiler/99.loader/*`
stubs and `src/compiler/test_pkg/mod.spl`), and a 0-byte file produces no
records, so the per-file counter never fires for it even though awk did open it.
The accounting now excludes empty targets (`expected_n = targets_n - empty_n`)
rather than false-ERRORing on a healthy tree. This is exactly the kind of
discrepancy the old `OK`-with-no-count verdict could never have surfaced.

Final full-repo verdict with the fix in place (`nice -n 19`, ~13 min):

```
check-dangling-references: FAIL -- 179 dangling reference(s) in 14685 file(s)
real-repo rc=1
```

Non-vacuous and honest: the count of files actually scanned is now part of the
verdict. The 179 findings are pre-existing content debt (including the two
false-positive classes documented above, which remain OPEN) and are not
addressed here.
