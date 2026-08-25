# `origin/main` is not test-runnable: `src/app/io/env_access_host.spl` fails to parse (2026-08-25)

**Status:** OPEN. **Not caused by the GPU hardening landing** (`8a291217121`) — reproduced on a
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

## Suggested guard
A pre-push check that parses the committed `src/app/**` + `src/lib/**` (e.g. `simple compile`
or a parse-only entry point) from a `git worktree` of the new tip — the `.spl` analogue of
`check-seed-builds-push.shs`, and fail-closed the same way.
