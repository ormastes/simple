# Stale deployed `bin/simple` seed could not parse origin's compiler source — redeploy 2026-08-17

**Status:** RESOLVED by redeploy (authorised explicitly by the user; a `bin/simple`
swap is normally forbidden because ~16 concurrent lanes depend on the binary).

## Symptom

The deployed binary was BEHIND origin and rejected compiler source that origin's
own parser accepts. Two arms over the identical bytes
(`git show origin/main:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
267543 bytes):

- parser built from current origin/main: `PROBE real_expr_dispatch: PARSED (267543 bytes)`
- deployed `bin/simple` (59536728 bytes, mtime 2026-08-16 22:59:37 UTC), rc=1:

```
error: compile failed (.../expr_dispatch_origin.spl): parse: in ".../expr_dispatch_origin.spl": Unexpected token: expected Fn, found Assign
```

The construct is module-level `var` initialisation at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:49-55` (`var x: text = ""`,
`var y: i64 = -1`, `var z: bool = false`, a bare `var w: i64`, and a `fn`
following a module-level `var`). All of these parse against origin's parser, so
**origin is correct and the deployed binary was stale** — this was a redeploy, not
a parser change.

## Blast radius

At least 7 pre-push guards native-build compiler source using `bin/simple`, so
this single parse failure took all of them down for EVERY lane regardless of what
that lane changed:

`check-predicate-parser-native-build`, `check-native-trailing-default-param`,
`check-native-object-cache-granularity`,
`check-native-inprocess-positional-nonvacuous`,
`check-render-perf-milestone-gate`, plus `check-lint-binary-staleness` and
`check-implicit-self-field-assignment`, which need a fresh binary to clear at all.

## What was built, and why the cheap path was the right one

Origin sha: `ade2871bbc07a6b0bbfa63ecaa7ab3bb1d789bdd`.

Built in an ISOLATED worktree (`git worktree add --detach`, 115397 files, clean)
— never the shared tree, which holds other lanes' uncommitted `src/compiler_rust`
edits including a known E0631 at `node_exec.rs:607` that would have contaminated
the build. `CARGO_TARGET_DIR=/mnt/data/cargo-target/redeploy-ade2871`.

```
cargo build --release --bin simple    # in src/compiler_rust
BUILD_RC=0
```

`.claude/rules/bootstrap.md` warns against hand-rolled `cargo build --release`
being copied to `bin/release/<triple>/simple`. That warning is about a fresh
**seed masquerading as a self-hosted binary**. It does not apply here, because
the binary already deployed WAS the Rust seed and said so — `bin/simple
--version` printed the seed WARNING banner before the swap and prints it after.
This is a seed replaced by a newer seed from origin; the provenance class did not
change, and nothing was made to look self-hosted that isn't. The full bootstrap
path is separately documented as blocked at Stage 3, so it could not have
produced a binary at all. The measured defect is in the RUST SEED's parser, which
is exactly what this build refreshes.

## Verification (before deploying)

- (b) `--version` rc=0 → `Simple Language v1.0.0-beta`
- (a) acceptance test, new seed on the identical file the old seed rejected:
  `grep -c 'Unexpected token: expected Fn, found Assign'` → **0**. The file now
  gets past parse and fails later, in semantic analysis only, with
  `Undefined("undefined identifier: HirExpr")` — expected for a single file
  compiled standalone out of its module, and the same error CLASS the old binary
  produced on the in-tree HEAD copy. The parse defect is gone.

Every rc above was read into a variable on the line AFTER the command, never
through a pipe: a pipe produced a false `TEST_RC=0` over a failing run earlier
today, because a pipeline's `$?` is the last stage's status.

## Deploy

`.new` + `mv` (a direct `cp` over a running binary hits "Text file busy"):

```
NEW: 59617400 bytes  mtime=2026-08-17 12:54:48 UTC
OLD: 59536728 bytes  mtime=2026-08-16 22:59:37 UTC
```

`/mnt/data/worktrees/simple-boot-snap` was not touched at any point.

## Rollback is one `mv`

```sh
mv bin/release/x86_64-unknown-linux-gnu/simple.pre-redeploy-20260817T125448Z \
   bin/release/x86_64-unknown-linux-gnu/simple
```

## Guard verdicts after the redeploy (verbatim last verdict line)

The blocker IS cleared: `grep -c 'expected Fn, found Assign'` over all 7 guard
logs returns **0** for every one. None of them is blocked by the stale parse
failure any more. They are now red for other, unrelated, real reasons:

| guard | rc | verdict line (verbatim) |
|---|---|---|
| predicate-parser-native-build | 1 | `FAIL — native-build of src/compiler/00.common failed` |
| native-trailing-default-param | 1 | `FAIL — native-build failed to compile the fixture (exit 1, log saved to /tmp/check-native-trailing-default-param.2768618.log)` |
| native-object-cache-granularity | 1 | `FAIL — cold native-build of the 3-module fixture did not succeed` |
| native-inprocess-positional-nonvacuous | 1 | `FAIL — in-process native-build exited non-zero; log: /tmp/check-native-inprocess-positional.2771836/inprocess-positional.log` |
| render-perf-milestone-gate | 1 | `check-render-perf-milestone-gate: FAIL — 7 of 28 milestone/identity example(s) failed on md5=c529a97fe5984e62b9a199f60e1b6174 (seed)` |
| check-lint-binary-staleness | 1 | `FAIL — deployed binary at bin/release/x86_64-unknown-linux-gnu/simple is STALE: missing 2 of 2 fresh marker(s): MEXH006 W-MC-RES-001 (present:)` |
| check-implicit-self-field-assignment | **2** | `ERROR — nothing was checked: engine 'interpreter': the CORRECT program (self.flag = true) failed with exit 1 — assertions would be vacuous: error: semantic: method `set_it_explicit` not found on type `object` (receiver value: C(flag: false))` |

Read carefully, these are three distinct outcomes and none is a pass:

- The four `native-build` guards now share ONE new root cause, not the old parse
  error: `error: semantic: method `compile` not found on type `object` (receiver
  value: CompilerDriver(...))`. That is a genuine content FAIL in origin/main's
  compiler source against this seed, and it is a separate defect that this
  redeploy neither caused nor fixes. It is the next thing to chase.
- `check-lint-binary-staleness` FAILing is **correct and expected**, and this
  redeploy could not have fixed it: it demands fresh markers `MEXH006` /
  `W-MC-RES-001` that only a self-hosted binary carries. The deployed binary is
  still the Rust seed, so this guard stays legitimately red until Stage 3
  self-host is unblocked. Refreshing the seed was never going to clear it.
- `check-implicit-self-field-assignment` is exit **2** — `ERROR — nothing was
  checked`. That is "could not determine", NOT a content verdict, and must not be
  reported as either a pass or a fail. Its own fixture cannot run because
  `self.flag = true` / `set_it_explicit` fails in the interpreter, which is again
  a separate defect.

No guard returned rc 143 or 137, so nothing here is unverified on that axis.

## Recurrence note

This is the same failure mode `.claude/rules/bootstrap.md` and
`.claude/rules/commands.md` already warn about from the other direction: a shared
`bin/simple` with no provenance gate drifts behind origin, and the drift is
invisible until something fails to parse. The lasting fix is not this redeploy —
it is Stage 3 self-host being unblocked so the deployed binary is a versioned
self-hosted artifact rather than an ad-hoc seed whose only recorded identity is
its mtime. Until then, every timing or verdict claim must record the binary's
size and mtime alongside it.
