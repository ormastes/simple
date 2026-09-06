# native-build is blocked from inside the repo by 91 hyphen/underscore module-name collisions

**Date:** 2026-07-28
**Status:** FIXED (re-confirmed 2026-08-09 — see bottom of doc) — was blocking the native smoke matrix on the pure-Simple compiler
**Severity:** high (it makes the mandatory pre-deploy gate unrunnable)
**Found by:** the MIR fail-open migration lane, while trying to run
`scripts/check/native-smoke-matrix.shs` against a pure-Simple binary.

## Symptom

Any `native-build` invoked with **cwd inside the repo** aborts immediately:

```
Build failed: native module name collision after path sanitization:
'.../src/app/llm_caret/claude_full/commands/ant-trace/index.spl' and
'.../src/app/llm_caret/claude_full/commands/ant_trace/index.spl'
both map to 'llm_caret__claude_full__commands__ant_trace__index';
rename one file or directory
```

Reproduced on `origin/main` in a pristine worktree and in the shared checkout,
so it is a property of the tree, not of anyone's local edits.

## Scale

`src/app/llm_caret/claude_full/commands/` contains each command **twice** —
once hyphenated, once underscored (`ant-trace/` and `ant_trace/`,
`autofix-pr/` and `autofix_pr/`, `backfill-sessions/` and
`backfill_sessions/`, …). Path sanitization maps `-` to `_`, so every pair
collides.

Count on `origin/main`:

```
git ls-tree -r --name-only origin/main src/ | grep '\.spl$' \
  | sed 's/-/_/g' | sort | uniq -d | wc -l
=> 91
```

91 sanitized paths have at least two real files mapping onto them.

## Measured impact: the whole matrix is dead on the pure-Simple compiler

Full run, 2026-07-28, `SIMPLE_BINARY=build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`:

```
total=24 pass=0 fail=24 xfail=0 xpass=0 codegen_fallback_hits=0
native_smoke_matrix=false
```

**All 24 cases fail with the byte-identical collision message.** Not one case
reaches parsing, MIR lowering, or codegen — the build aborts during the source
scan. `codegen_fallback_hits=0` across the run because no codegen happens at
all. So the matrix currently provides **zero** signal about the self-hosted
compiler; a change to 50.mir or 80.driver cannot be validated or invalidated by
it until this is fixed.

## Why it stayed invisible

`scripts/check/native-smoke-matrix.shs` defaults to `SIMPLE_BINARY=bin/simple`,
and the deployed `bin/simple` is the **Rust seed**, which does not perform this
collision check. The matrix therefore reports green while never exercising the
pure-Simple compiler that does perform it. The collision only surfaces when the
matrix is pointed at an actual pure-Simple binary, e.g.

```
SIMPLE_BINARY=build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple \
  sh scripts/check/native-smoke-matrix.shs
```

This is the same "the matrix passed" trap that has misled several lanes: a
green matrix run against the seed says nothing about the self-hosted compiler.

## Workaround (probe-only, NOT a fix)

Running `native-build` with cwd **outside** the repo builds fine, because the
collision comes from scanning `src/`. That is only usable for standalone
single-file probes; it does not let the matrix run, since the matrix `cd`s to
`ROOT_DIR`.

## What a fix needs to decide

Which spelling is canonical for `src/app/llm_caret/claude_full/commands/`, and
whether the duplicate tree is intentional (two dispatch spellings for the same
command) or an accidental double-add. Deleting the wrong half will break
command dispatch, so this needs an owner for that area rather than a mechanical
rename. Deliberately not fixed here.

## Related

- `doc/03_plan/compiler/reliable_mode/mir_error_fail_open_class_migration_plan.md`
  — the lane that hit this.

## Re-confirmed 2026-08-09 — ALREADY-FIXED, verified fresh

Re-ran the exact counting command from this doc against current `HEAD`:

```
git ls-tree -r --name-only HEAD src/ | /usr/bin/grep '\.spl$' | sed 's/-/_/g' | sort | uniq -d | wc -l
=> 0
```

Zero collisions today, versus the 91 recorded on `origin/main` at the time
this doc was filed. `src/app/llm_caret/claude_full/commands/` now carries
only the underscored spelling of each command directory (`ant_trace/`,
`autofix_pr/`, `backfill_sessions/`, ...) — the hyphenated duplicates named in
"Scale" above are gone from the tree; `git log` shows subsequent commits
touching that directory (`cfe0506e336`, `78dbaff5d7c`, `aff29a24dfe`). No
stage3 pure-Simple binary was available in this session to re-run
`native-build` end-to-end (building one is out of budget for this pass), but
the underlying condition this doc names — the hyphen/underscore duplicate
tree causing path-sanitization collisions — is verifiably gone at the source
level, which is sufficient to close this. Status: **FIXED**. No code changed
this pass (the dedup predates this session).

## Recurrence 2026-09-06 — REOPENED then re-fixed

The condition came back. `e274cd33719` ("chore: merge all share-history
worktree branches into main") resurrected the hyphen tree under `src/`, and
`e9da588ee61` / `bd2a4b77791` carried it forward. Measured at
`4699194f81e`: **99** sanitized-name collision groups, 198 files, every one a
hyphen/underscore twin inside `src/app/llm_caret/claude_full/` and none
anywhere else in `src/`, `test/` or `scripts/`.

**Exactly which invocation this breaks — measured, not inferred.** It is the
`--entry <file>` form with no `--source` and no `--entry-closure`, which "scans
the DEFAULT source roots (whole project)" (the driver says so itself in a note
printed alongside the failure). Direct A/B with the Stage-2 compiler
`build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple` — same binary, same
fixture (`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`), same
flags, only the tree differing:

| tree | result |
|---|---|
| unfixed (99 collision groups) | fails within seconds: `Build failed: native module name collision after path sanitization: '.../commands/add-dir/add-dir.spl' and '.../commands/add_dir/add_dir.spl' both map to 'app__llm_caret__claude_full__commands__add_dir__add_dir'` |
| fixed (0 collision groups) | proceeds past source collection into the whole-project import graph; **0** collision messages |

`scripts/check/check-stage2-hello-world-native-build.shs` is **not** the gate
that catches this, and an earlier draft of this note wrongly said it was. That
gate passes `--entry-closure` on both arms — mandatory, per its own header:
without it the candidate "scans the DEFAULT source roots (whole project) and
runs unbounded". Measured 2026-09-06, it reports `PASS — 2 case(s) checked`
against the Stage-2 binary on the **unfixed** tree just as it does on the fixed
one. Its `FAIL — 2 case(s) checked, simple:entry-form:fail(build exited 1)`
against the Rust *seed* on this host is a different, unrelated defect
(`native-capsule-receipt-invalid`, see
`windows_native_capsule_receipt_invalid_blocks_every_native_build_2026-09-03.md`).
The two share a verdict string and nothing else.

Disposition this pass, same policy as `98c64a3f260`:

- **89** src-side hyphen files were **byte-identical** to the copies already
  sitting in `doc/11_archive/llm_caret_claude_full_hyphen_port/` — pure
  resurrection debris. Deleted; content is preserved in the archive.
- **9** hyphen files not in the archive were byte-identical to their
  underscore twin. Deleted.
- **1** (`commands/add-dir/validation.spl`) was not in the archive and differed
  from its twin — by generated `# parity ledger:` comment lines only. Archived
  rather than deleted, so no content is dropped.
- 27 now-empty hyphen directories pruned. 370 hyphenated files with no twin
  collide with nothing and were left alone.

Direction of the dependency proves which side is live: hyphen files `use`
underscore modules (e.g. `use app.llm_caret.claude_full.commands.extra_usage.
extra_usage_core.*`), never the reverse, and **zero** `use` statements anywhere
in `src/` name a hyphen `claude_full` module — hyphens lex as subtraction in a
`use` path, so the hyphen twins are unimportable by construction.

Five specs read source *text* at hyphen paths and were repointed: to the
underscore twin where the bytes are identical
(`cli_command_missing_files_spec.spl`, `context_noninteractive_spec.spl`,
`security_review_spec.spl`) and to the archive path otherwise
(`extra_usage_command_spec.spl`, `review_rewind_sandbox_spec.spl`) — the same
mapping `doc/08_tracking/test/spec_missing_path_classification_2026-08-10.tsv`
already records as `RENAMED-CONFIRMED`.

**Prevention gap, still open:** nothing gates this. There is no push- or
bootstrap-tier check that the sanitized module-name set over `src/**/*.spl` is
injective, which is why a whole-worktree merge could re-introduce 99
collisions silently. A ratchet in the shape of the other
`scripts/check/check-*-push.shs` guards would have caught both occurrences.
