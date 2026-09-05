# Investigation: reported stage4 `export use X.{a,b,c}` parse failure — NOT a general main-branch regression

Status: **investigated, verdict: environmental to one worktree's stage3 artifact, not a source-level grammar defect on main.** No fix needed on `main` for the parsing question itself; original bug (`rt_fork_parent_wait_bounded` truncation) is unaffected and still needs its own stage-4 rebuild to verify.

## What was reported

`doc/08_tracking/bug/stage4_test_runner_pipe_capture_truncation_rt_fork_2026-07-20.md`
(committed `c3e3204485` in `/tmp/wt_deploy`) reports that during a
`--full-bootstrap` rebuild, the freshly-(cargo-)rebuilt seed's stage2/stage3
chain fails stage 4 (`bootstrap_native_build_main`, i.e.
`<stage3> native-build --entry src/app/cli/main.spl ...`) with
`expected field name after '.'` at `src/app/cli/main.spl:15:30`, on an
untouched line:

```
export use std.cli.log_modes.{parse_log_options, log_options_help, render_progress}
```

Reported reproducible twice in that worktree (same stage3 binary reused both
times — not two independent builds).

## Investigation (fresh, clean worktree at origin/main `be52c00729f`)

1. **Syntax validity.** `simple lex`/`simple check` (deployed, checked-in
   release binary, `bin/simple --version` → `v1.0.0-beta`) parse and
   type-check `src/app/cli/main.spl` cleanly, and correctly tokenize the
   brace-list at column 30. Minimal repro variants (`export use` vs plain
   `use`, 2 vs 3 names, trailing comma) all lex/check clean.
   **Caveat**: this binary is dated Jul-19, predating today's commits — it
   proves the syntax is valid, not that today's fresh build parses it.
2. **Ubiquity.** `use X.{a,b,c}` (any form) appears 21,116 times in `src/`;
   `export use X.{a,b,c}` specifically appears 245 times inside
   `src/compiler` alone (e.g. `src/compiler/00.common/__init__.spl:66`,
   3-name-braced shape identical to `main.spl:15`). A genuine grammar
   regression in the freshly-built chain would have to break parsing of
   `src/compiler` itself — the exact source stage2 must consume to produce
   stage3.
3. **Internal consistency of the original report.** The report states stage 2
   and stage 3 *succeeded* in the same run. Since `src/compiler` already
   contains 245 `export use X.{...}` sites including the identical
   multi-name-braced shape, a successful stage2/3 self-compile is only
   possible if the freshly-rebuilt chain already parses this exact
   construct correctly. The stage4 failure on the same construct, using the
   *same* stage3 binary, is therefore best explained by something specific
   to that worktree's stage3 artifact or stage4 invocation state — not a
   grammar hole in the parser.
4. **Bisect of named suspect commits** (8ec74920627, 9a6c9c51cf8,
   8699cca54b6, b66544abf59, 3acd95d27fb, c12f965ba50, a8674698e23): none
   touch `use`/`export use` import-statement parsing. `c12f965ba50`
   ("export-use removal") in particular only touches a bug doc and a test
   spec in this commit (`git show --stat` → 2 files, both docs/tests); the
   actual `cli_ops.spl` export-use edit it describes landed in an earlier
   commit and is source-level (changes what a file re-exports), not a
   parser/grammar change — it cannot cause a misparse of an unrelated file.
   `8ec74920627` touches Rust-seed `native_project/imports.rs`, but stage 4
   runs under the **stage3 self-hosted binary**, not the Rust seed, so this
   is not in the code path either.
5. **Direct repro attempt** (replicating `bootstrap_native_build_main`'s
   exact `native-build --entry-closure --mode one-binary --entry
   src/app/cli/main.spl ...` invocation against the deployed binary):
   segfaulted immediately in this fresh worktree — but for an unrelated,
   mundane reason: no `src/compiler_rust/target/bootstrap` runtime-bundle
   directory exists here (no cargo build has been run in this worktree), and
   `--runtime-path`/`SIMPLE_RUNTIME_PATH` were therefore missing/invalid.
   This is a control-setup gap, not evidence about the parser. A full,
   faithful control build (fresh `cargo` seed rebuild + stage2 + stage3 +
   stage4 from this clean worktree) was **not completed** — it does not fit
   in a single bounded, non-backgrounded tool call in this repo (bootstrap is
   a multi-hour operation per prior session notes), so the clean-tree
   positive control is still outstanding.

## Verdict

**Not a general bootstrap-breaking regression on today's main.** The
construct is syntactically valid, ubiquitous, present (in the exact shape)
inside the very source tree that stage2/3 already had to parse successfully
in the same reported run, and none of today's parser-adjacent-looking
commits actually touch import/use-statement grammar. The most consistent
explanation is a bad/stale stage3 artifact or stage4-local state specific to
`/tmp/wt_deploy`'s interrupted+rerun `--full-bootstrap` session (that session
also independently records a backgrounded run started before the
"no background" rule was enforced, and a stage4 step that deletes the prior
good binary before confirming the replacement — both consistent with a
contaminated worktree rather than a clean one).

This verdict is **not proven by a completed clean full-bootstrap** (that
control did not fit in budget); it rests on the structural/internal-
consistency evidence in items 2-4 above, which is strong but indirect. If a
future session needs certainty, the settling test is: from a clean worktree,
run a full `--full-bootstrap` (cargo rebuild + stage2 + stage3 + stage4) to
completion and confirm stage 4 parses `main.spl` — a multi-hour operation
that should be scheduled as its own bounded task, not folded into a quick
follow-up.

## Recommendation for the blocked lane

The `runtime_fork.c` fix in the original doc is a C-only semantic change and
is not implicated by this investigation. It remains blocked on a successful
stage-4 rebuild, but that block is very likely a worktree-local artifact
problem in `/tmp/wt_deploy`, not a defect to fix on `main`. Recommend: retry
the stage-4 rebuild in a **fresh** worktree/cache (not the contaminated one)
before spending more time hunting for a phantom grammar regression.
