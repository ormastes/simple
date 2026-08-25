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

## Guard (landed 2026-08-25) — `scripts/check/check-main-test-runnable-push.shs`

The guard suggested here now exists and is wired as a blocking `push` row
(`push-main-test-runnable`) in `config/check/must_check_gates.sdn`. It materialises the
pushed tip with `git worktree add --detach` and runs `test/fixtures/doctest/green.md`
inside it; verdict convention matches the other pre-push guards, and a missing binary,
missing fixture, or unmaterialisable worktree is ERROR, never a pass.

**It is narrower than this section originally asked for, and is named for what it checks.**
A trivial doctest opens ~82 stdlib sources, not the ~14k `.spl` in the tree, so the
invariant is "the committed tree is test-runnable", not "every committed `.spl` parses" — a
syntax error in a module nothing loads at startup still gets through. That is a deliberate
cost trade: `simple lint` over the tree is unaffordable per push (superlinear per-declaration
cost, `.claude/rules/commands.md`), whereas this pays the compiler's startup path once, which
is the path this incident broke and the one whose failure invalidates every other session's
test evidence. The whole-tree parse sweep remains a separate, more expensive guard that does
not yet exist.

Cost ~70s cold, 0.1s warm. Skips are positive-proof only: a content-keyed green marker over
the git tree ids of `src/app` + `src/lib` + the fixture, the same pattern as
`check-seed-builds-push.shs`, so a skip means "this exact content already ran green here",
never "the range looked unrelated".

Selftest fatal, 6 fixtures. Two near-misses during development are worth recording, because
each would have produced a guard that passed forever:

- Matching only a non-zero exit made the incident-replay fixture vacuous. A fresh worktree
  has no `bin/simple` (gitignored symlink) and the doctest runner spawns a CHILD compiler
  from that path, so every block failed with or without the injected bug — which briefly made
  this guard report a healthy `origin/main` as broken. The guard now provisions the symlink,
  fixture C1 requires the clean worktree to run green first, and C2 requires the failure
  detail to NAME the parse error.
- If stdlib resolution ever escapes the tree under test (the nested-`.git` mode where a
  binary read `src/lib` from an unrelated worktree), C2 goes green and the fatal selftest
  stops the run.

Verified on `origin/main` at `c2504144e5a`: `PASS — 1 fixture invocation executed ... tree is
test-runnable`.

## Resolution (2026-08-25, same day)

The parse abort is FIXED. `src/app/io/env_access_host.spl` had the closing `)` of the multi-line
`rt_hal_install_isolated_exact_host_from_plan(...)` call moved **past the following `pub fn`** to
the end of the file, so the argument list never closed and the parser met `pub` where it wanted a
comma. The call passes exactly the callee's nine parameters
(`src/app/io/rt_hal_isolated_host.spl:237-241`), so restoring the paren to its own line after
`loaded.max_output_bytes` and deleting the stray trailing line is the whole fix — one line moved.

Two further blockers were found behind it and fixed here as well:

1. `rt_env_cwd` infinite recursion —
   `doc/08_tracking/bug/rt_env_cwd_wrapper_shadows_extern_infinite_recursion_2026-08-25.md`.
   With 1 and 2 fixed, `bin/simple todo-scan` runs on clean `origin/main`: `239 TODOs found`
   (it previously died with a depth-1000 stack overflow).
2. A variable named `namespace` was rejected by the "common mistake" detector
   (`test_runner_mcdc_report.spl:331`), renamed to `ns_hash`.

**`bin/simple test` on clean content now WORKS.** With the two fixes above, a clean `origin/main`
worktree runs `test/fixtures/doctest/green.md` to `SDoctest Results: 1 total, 1 passed`. (A bare
worktree additionally needs a built binary present for the sdoctest subprocess; that is normal, not
a defect.) The `dict[Ctor(...)]`-read-as-generics diagnostics that accompanied this were
warning-level noise, not a blocker, and are now fixed too —
`doc/08_tracking/bug/common_mistake_detector_false_positive_dict_index_ctor_2026-08-25.md`.

**Unrelated finding worth acting on:** a fresh `todo-scan` of clean `origin/main` yields 239
entries while the committed `doc/08_tracking/todo/todo_db.sdn` holds roughly 741 lines' worth —
the checked-in database does not match its own source. It was deliberately NOT regenerated here,
because replacing it from any single tree would silently delete entries other sessions rely on.
