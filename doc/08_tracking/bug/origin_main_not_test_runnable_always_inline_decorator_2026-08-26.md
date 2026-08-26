# `origin/main` is not test-runnable: `unknown decorator @always_inline` on a startup-path stdlib file (2026-08-26)

**Status:** OPEN, RED on `origin/main` right now. Found by
`scripts/check/check-main-test-runnable-push.shs`, the guard landed for the *previous* instance of
this exact class (`origin_main_not_test_runnable_env_access_host_parse_2026-08-25.md`) — its first
real catch, hours after landing.

## Symptom

A fresh worktree of `origin/main` cannot run `bin/simple test` at all. Even the trivial
`test/fixtures/doctest/green.md` aborts before executing anything:

```
error: semantic: unknown decorator `@always_inline` on function `_file_mmap_read_text_raw`
```

Guard verdict:

```
check-main-test-runnable-push.shs: FAIL — 1 fixture invocation executed at 29043439c50,
  tree is NOT test-runnable: rc=1: error: semantic: unknown decorator `@always_inline` ...
```

## Where

`src/lib/nogc_sync_mut/io/file_ops.spl:34` — `@always_inline` on `_file_mmap_read_text_raw`, and
again a few lines below on `_file_hash_sha256_raw`. Introduced by `16acb87b835 fix(sffi): type
file size and digest failures`. This file is on the compiler's startup path, so the rejection
aborts every `test` invocation regardless of what is being tested.

## What is NOT the problem

`@always_inline` is **not** an unknown decorator to the deployed compiler in general. Both of
these run clean on `bin/release/x86_64-unknown-linux-gnu/simple` (2026-08-25 06:08):

```
@always_inline
fn f() -> i64: 7                                    # runs, prints 7

extern fn rt_file_mmap_read_text(path: text) -> text?
@always_inline
fn g(path: text) -> text?:                          # the exact shape of the failing function,
    unsafe(capabilities: [ffi]):                    # including the optional return and the
        rt_file_mmap_read_text(path)                # unsafe block -- runs clean
```

So it is neither the decorator alone nor the function's shape. The rejection is specific to the
**stdlib load path** (and/or the `test` engine — the probes above were run under `bin/simple run`,
which is the Cranelift JIT, while the failure is under `test`, the tree-walk interpreter; those
are different engines per `.claude/rules/testing.md`). `src/compiler/10.frontend/parser_types_expr.spl`
also uses `@always_inline` without complaint, but nothing loads it during a doctest, which is
consistent with a load-path-scoped decorator allowlist. **The exact mechanism is not pinned** —
stated rather than guessed at.

## Fix options

1. Drop the two `@always_inline` decorators from `file_ops.spl`. They are an optimisation hint;
   removing them restores a runnable `main` and costs nothing semantically. Smallest safe change,
   but it reverts part of another session's in-flight work, so it should be their call if they are
   still active.
2. Whitelist the decorator on the stdlib load path in the seed — correct if the decorator is meant
   to be usable there, but needs a seed rebuild and does not unblock today.

Not done here because this is another session's active work and the mechanism is unpinned; filing
rather than editing over them. See `.claude/memory/never-kill-others-work.md`.

## Consequence for the push gate

`push-main-test-runnable` was landed as a **blocking** gate. With `main` red, it blocks *every*
session's push for a breakage they did not cause. It is therefore switched to non-blocking
(`push_blocking: false`) in `config/check/must_check_gates.sdn` until this is fixed — the same
"land ADVISORY because it is honestly RED" precedent the stage-binaries and unresolved-symbols
guards set in `.claude/rules/vcs.md`. It still runs and still reports on every push; it just does
not block. **Promote it back to `true` in the same change that makes `main` green** — an advisory
guard nobody promotes back is how a ratchet quietly stops ratcheting.

## Guard hardening this exposed

The first cut of the guard's selftest required the tree to run green (fixtures A and C1 as
absolute checks). That meant a genuinely broken `main` turned the guard into
`FAIL — selftest failed; no scan was run`, **suppressing the very report it exists to make** — it
stopped working exactly when it was needed. Fixed in the same change: A is now a non-fatal note,
and C1/C2 are a **differential** (inject the paren bug, require a parse diagnostic that the clean
run did not produce), which needs no healthy baseline. C1 still fails honestly if the clean run
*already* shows a parse error, since injection would then prove nothing.
