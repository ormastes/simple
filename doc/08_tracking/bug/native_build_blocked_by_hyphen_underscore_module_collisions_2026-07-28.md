# native-build is blocked from inside the repo by 91 hyphen/underscore module-name collisions

**Date:** 2026-07-28
**Status:** OPEN — blocks the native smoke matrix on the pure-Simple compiler
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
