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
