# `--spl-doctest` aborts on every input at origin/main — `function `unsafe` not found`

Status: OPEN. Severity: HIGH — **every** `--spl-doctest` run at origin/main tip
produces no verdict line, so every SPL doctest result at that tip is UNKNOWN,
neither pass nor fail.

## Symptom

At `origin/main` = `6cd4f9a3381`, from a clean `git worktree add --detach`:

    $ ./bin/simple test --spl-doctest src/lib/nogc_async_mut/http_server/cors.spl
    === Running SPL Doctests ===
    SPL Doctest: Running doctests from 1 source file(s)...
    error[E1002]: function `unsafe` not found
      = help: check the function name or import the module that defines it
    EXIT=1

    $ ./bin/simple test --spl-doctest src/lib/nogc_async_mut/http_server/csrf.spl
    SPL Doctest: Running doctests from 1 source file(s)...
    error[E1002]: function `unsafe` not found
    EXIT=1

Both files were probed independently; neither contains the token `unsafe`
(`grep -n unsafe cors.spl` -> no hits). The abort is therefore not
file-specific — it is in the harness's own module graph.

**There is no `SPL Doctest: N passed, M failed, K skipped` line.** Per
`.claude/rules/testing.md`, a run with no results line aborted and its counts
are UNKNOWN. Note `EXIT=1` is reported by the wrapper while the process itself
is recorded as `exited with code 0`; the missing verdict line, not the exit
code, is the load-bearing evidence.

## Not reproducible at an older tip — the harness works there

Same binary, same command, cwd at `8a47377b696`:

    $ ./bin/simple test --spl-doctest src/lib/nogc_async_mut/http_server/cors.spl
    SPL Doctest: Running doctests from 1 source file(s)...
    SPL Doctest: 0 passed, 1 failed, 0 skipped
    EXIT=1

A real verdict line, a real failure. Since the stdlib is read as SOURCE
cwd-first on every run (see `.claude/rules/commands.md`), the difference is in
repository source between `8a47377b696` and `6cd4f9a3381`, not in the binary.

Binary identity for every transcript in this record:

    $ readlink -f bin/simple
    /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
    $ stat -c '%s %y' "$(readlink -f bin/simple)"
    60650360 2026-08-23 04:47:05.208206071 +0000

This is the Rust bootstrap seed (it says so on `--version`). The same seed
produces a verdict at `8a47377b696` and none at `6cd4f9a3381`, which is what
isolates the regression to source.

## Why this matters beyond doctests

Any lane that runs `--spl-doctest` at current `main` and reads a non-zero exit
as "N doctests failed" is reading a fabricated number. The run never got far
enough to execute a doctest. This is the same failure shape as the
already-recorded preflight-abort defect (`f910634dc3c`, "a run with no
Results: line aborted; its counts are UNKNOWN") in a different harness.

## Not yet done

The culprit commit in `8a47377b696..6cd4f9a3381` has not been identified. A
bisect at roughly 1-5 min per run was out of scope for the lane that found
this. The two endpoints above are exact and reproducible, so a bisect is
mechanical whenever someone picks it up. The harness itself is
`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl`.

## Consequence for the aspirational-doctest work

All doctest fixes landed alongside this record were verified under the
`8a47377b696` harness, not at origin/main, because at origin/main no doctest
verdict can be obtained at all. `git diff --stat 8a47377b696 6cd4f9a3381` over
the touched directories shows only `http_server/static_file.spl` and
`io/metal_ptr.spl` differing — neither is a file this work edits — so the
transferred verification is clean. That caveat is stated rather than papered
over.
