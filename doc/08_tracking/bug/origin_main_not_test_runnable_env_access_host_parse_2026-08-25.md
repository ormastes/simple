# `origin/main` is not test-runnable: `src/app/io/env_access_host.spl` fails to parse (2026-08-25)

**Status:** SUPERSEDED. **Not caused by the GPU hardening landing** (`8a291217121`) — reproduced on a
clean worktree of `origin/main` with two independent binaries, including one that predates it.

## Symptom
In a **fresh** `git worktree` of `origin/main` (tip `baf0597bd78`), any `bin/simple test <spec|md>`
— including the trivial `test/fixtures/doctest/green.md` — aborts before executing anything:

```
error: compile failed: parse: in ".../src/app/io/env_access_host.spl":
       function arguments: expected Comma, found Pub
```

Both binaries agree, so this is the tree, not one build:

| binary | in the shared working tree | in a fresh `origin/main` worktree |
|---|---|---|
| deployed `bin/release/x86_64-unknown-linux-gnu/simple` (2026-08-25 06:08) | doctest **PASSES** | **FAILS** (this error) |
| fresh `cargo build --release --bin simple` from `origin/main` (08:10) | fails on the shared tree's own stale `tooling/easy_fix/accessor_rewrite.spl` | **FAILS** (this error) |

The shared working tree only appears healthy because it is *behind* origin on these files:
`git diff origin/main -- src/app/io/env_access_host.spl` is `255 deletions` (the tree does not
have the version origin does), and `accessor_rewrite.spl` differs by 7 lines.

## Why no guard caught it
`check-seed-builds-push.shs` runs `cargo check` — it compiles the **Rust**, and never parses a
`.spl`. Nothing in the pre-push set loads the stdlib/app sources with the compiler, so a `.spl`
syntax regression in `src/app/**` or `src/lib/**` lands green and only surfaces when someone runs
`test` against committed content.

Last commit touching the file: `98215e0f708 feat: implement MC/DC RT HAL hardening`.

## Impact
A fresh clone of `main` cannot run its own test suite. Every session currently reporting green
tests is doing so against a working tree that differs from `main`.

## Guard (landed 2026-08-25) — `scripts/check/check-main-test-runnable-push.shs`

The suggested guard now exists and is wired as a blocking `push` row
(`push-main-test-runnable`) in `config/check/must_check_gates.sdn`.

It materialises the pushed tip with `git worktree add --detach` and runs
`test/fixtures/doctest/green.md` inside it. Verdict convention matches the other
pre-push guards (`PASS`/`FAIL` 1/`ERROR — nothing was checked` 2); a missing binary,
missing fixture, or unmaterialisable worktree is ERROR, never a pass.

**It is narrower than this record originally asked for, and is named for what it checks.**
A trivial doctest opens ~82 stdlib sources, not the ~14k `.spl` in the tree, so the
invariant is "the committed tree is test-runnable", not "every committed `.spl` parses".
A syntax error in a module nothing loads at startup still gets through. That is a
deliberate cost trade: `simple lint` over the tree is unaffordable per push
(superlinear per-declaration cost, see `.claude/rules/commands.md`), whereas this pays
the compiler's startup path once — the exact path this incident broke, and the one whose
failure invalidates every other session's test evidence. A whole-tree parse sweep remains
a separate, more expensive guard that does not yet exist.

Cost: ~70s cold; 0.1s on the fast path. Skips are positive-proof only — a content-keyed
green marker over the git tree ids of `src/app` + `src/lib` + the fixture, the same
pattern as `check-seed-builds-push.shs`, so a skip means "this exact content already ran
green here", never "the range looked unrelated".

Selftest is fatal, 6 fixtures. The load-bearing one (C2) re-injects this incident's exact
unclosed-paren shape into the worktree's own `env_access_host.spl` and requires a FAIL
whose detail NAMES the parse error. Two near-misses are worth recording, because both
would have produced a guard that passed forever:

- Matching only a non-zero exit made C2 vacuous: a fresh worktree has no `bin/simple`
  (gitignored symlink) and the doctest runner spawns a CHILD compiler from that path, so
  every block failed with "Process failed to start or returned an internal error" —
  with or without the injected bug. This briefly made the guard report a healthy
  `origin/main` as broken. The guard now provisions the symlink, and fixture C1 requires
  the same clean worktree to run green *before* C2 injects.
- If stdlib resolution ever escapes the tree under test (the nested-`.git` failure mode,
  where a binary read `src/lib` from an unrelated worktree), C2 goes green and the fatal
  selftest stops the run.

Verified on `origin/main` at `c2504144e5a` after the fix in `a8a32ebccad`:
`PASS — 1 fixture invocation executed ... tree is test-runnable`.

Status: the original defect is FIXED (`a8a32ebccad`) and the class is now guarded.

## 2026-11-10 status — SUPERSEDED (P3 library lane, work/p3-lib-20261110)

Re-verified on this lane's base (origin/release/1.0.0, which contains
`a8a32ebccad`): the env_access_host.spl parse failure does not reproduce. The
guard fixture `test/fixtures/doctest/green.md` was executed with the deployed
seed from a clean lane worktree — the run compiled and progressed past parsing
to runtime stages (it stops on a Windows-seed-only gap: `unknown extern
function: rt_io_file_open_read`, a seed registration gap unrelated to this
record). The parse regression is fixed and guarded as the record states.

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Re-verified with this lane's refreshed seed (bin/simple.exe, build-commit
`0791c2b7f4a7`, seed-smoke): `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
$PWD/bin/simple.exe test test/fixtures/doctest/green.md --mode=interpreter
--no-cache` → full `PASS (1 passed, 0 skipped, 83ms)`, rc=0 — no parse
failure at `env_access_host.spl`, and no Windows-seed extern stop either
(the 2026-11-10 lane stopped at `rt_io_file_open_read`; the 2026-11-11
seed completes the doctest). Original defect fixed in `a8a32ebccad`
(ancestor of this base); guard `check-main-test-runnable-push.shs`
remains the class gate. Env-facade lens: the failure class was
parse-level, not a raw env read; the guarded invariant is the committed
tree staying test-runnable.
