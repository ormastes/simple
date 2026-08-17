# `expr_dispatch.spl` does not parse: `expected Fn, found Assign` — blocks every push

- **Status:** OPEN, UNLOCALIZED. Blocks the pre-push hook for every lane.
- **Found:** 2026-08-17, while fixing a *different* parse error in the same guard.
- **Not fenced:** new row, not one of the `CLAIMED-OFFHOST 2026-08-17` set.

## Symptom

```
error: compile failed: parse: in
  "src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl":
  Unexpected token: expected Fn, found Assign
```

`check-native-trailing-default-param.shs` is RED on pristine `origin/main`
because of this. The parser reports **no line or column**, which is the main
reason this is expensive to localize.

## This is a SECOND, INDEPENDENT cause of that guard's RED

The fence notice attributed the guard's RED solely to
`src/compiler/50.mir/verification_semantic_coverage.spl` (`d9dfcbf80e0`). That
file was a real defect and is fixed (wrapped or-patterns; see
`parser_or_pattern_no_line_continuation_2026-08-17.md`). **Fixing it is not
sufficient** — the guard then fails again here, in a different file with a
different message. Anyone told "fix that file and the hook unblocks" should
expect a second RED.

## Reproduction

```bash
git worktree add --detach /tmp/wt origin/main && cd /tmp/wt
ln -sfn <path-to-existing>/bin/release/x86_64-unknown-linux-gnu/simple bin/simple
bin/simple run src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl 2>&1 \
  | grep "expected Fn, found Assign"
```

Reproduces directly (no native-build needed), so it is not a daemon or
scheduling artifact. Takes >120s on the intact 4483-line file.

## Dead ends already ruled out — do not repeat these

- **Prefix-truncation bisect is UNSOUND here.** The predicate is not monotonic:
  truncating mid-construct invents unrelated errors. It "converged" on line 49
  (`var mir_lower_parent_expr_file: text = ""`); that is an **artifact**.
- A minimal module-level `var g: text = ""` parses fine. So do
  `extern fn`+`var` and `extern fn`+`fn`+`var`. Line 49 is innocent.
- `me` is NOT a corruption of `fn` — it is the standard method keyword
  (2918 occurrences under `src/compiler/`). Line 117's `me ...` is fine.
- No stray assignment at impl-body indent: every `^    ` non-comment line after
  `impl MirLowering:` (line 116) is `me `/`fn `. Checked exhaustively.
- No stray module-level (col-0) statement: only `use`/`fn`/`extern`/`impl`/`var`
  /`pub fn`.
- No `pub var`/`pub val`. No tabs. No odd 1-3 space indents.
- No attributes/decorators in the file, so the known
  `parser_rejects_pub_union_after_attribute_2026-08-10` /
  `parser_rejects_trait_after_argumented_attribute_2026-08-10` shape
  (both also "expected Fn") does NOT apply here.
- Not the trailing-`|` continuation bug: the only trailing `|` in the file is
  inside a comment (line 4278).
- Siblings in `_MirLoweringExpr/` have no trailing-`|` defect either.

## Untested leads, cheapest first

1. **Misattribution.** The message may name `expr_dispatch.spl` while the real
   defect is in a sibling pulled in via its `use compiler.mir.mir_lowering_expr.*`
   (line 2), which in turn does `export use compiler.mir._MirLoweringExpr.*`
   (`mir_lowering_expr.spl:15`) — a re-export cycle through
   `switch_operators_calls.spl` / `method_calls_literals.spl` / `literals.spl`.
   Parse each sibling individually and see which one actually reports it.
2. **`_MirLoweringExpr/` has no `__init__.spl`** while sibling package dirs under
   `50.mir/` do. Probably unrelated to a *parse* error, but it is an anomaly in
   the same directory and cheap to check.
3. **Bad wipe-restore.** `git log -L49,49` attributes this region to
   `ae55a7467197` "fix(vcs): restore tree wiped by 6f86ff32a7d". Diff the file
   against its pre-wipe version — if this is a restore artifact, restoring
   known-good content is far cheaper than hand-editing 4483 lines.
4. Delete-one-method localization (49 methods) is sound but costs >120s per
   run, ~100 min serial. Use it only after 1-3 fail.

## Do NOT

- Do **not** `--no-verify` past this. Nine mandatory guards; two unbuildable
  trees reached `main` today exactly that way.
