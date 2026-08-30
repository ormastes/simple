# Deployed compiler cannot parse main's `unsafe(capabilities:)` syntax

Status: open
Found: 2026-08-30, in a clean worktree detached at `origin/main` (8e821cee0d6).

## Symptom

`bin/simple test <any spec importing app.io.mod>` fails before running a single
example:

```
error: compile failed: parse: in ".../src/app/io/mod.spl":
  Unexpected token: expected Newline, found Identifier { name: "rt_random_uniform" }
```

Reproduced on a PRISTINE checkout of `origin/main` with no local edits, using an
untouched pre-existing spec (`test/01_unit/app/tooling/context_generate_spec.spl`),
so it is not caused by any in-flight change.

## Cause

`origin/main:src/app/io/mod.spl:119-126` uses the capability-safety forms:

```
@unsafe(reason: "raw scalar random provider ABI", capabilities: [ffi])
extern fn rt_random_uniform(min: f64, max: f64) -> f64

fn random_uniform(min: f64, max: f64) -> f64:
    unsafe(capabilities: [ffi]): rt_random_uniform(min, max)
```

The deployed binary predates that grammar:

```
bin/release/x86_64-unknown-linux-gnu/simple   built 2026-08-26 01:16
```

So the tree is ahead of the compiler that is supposed to build it. The source is
not malformed — the parser is old.

## Why it stayed invisible

The shared working tree `/mnt/data/worktrees/simple-main` is a DIVERGENT older
generation whose `mod.spl` still has the bare `extern fn` form with no `@unsafe`
attribute. Specs run green there and fail on `origin/main`, so local runs prove
nothing about what CI or a fresh clone sees. Two separate investigations on
2026-08-30 were misled by that same divergence before this was isolated.

## Impact

`app.io.mod` is imported across the app tree, so `bin/simple test` cannot execute
those specs against committed content. Per CLAUDE.md a `src/lib/**` change needs
no build, but this is a GRAMMAR change: it needs a redeployed compiler, and the
bootstrap redeploy is separately blocked (see
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`, where all
four tracked stage binaries SEGV on hello world).

Note `bin/simple run` is NOT affected for code that avoids the new syntax — the
BM25 log-summary mode added alongside this record runs correctly end to end
(137,245 B -> 370 B) via `run`; only `test` on `app.io.mod` importers is blocked.

## Fix

Redeploy a compiler built from current `main` (unblocking the stage-binary SEGV
first), then re-run the affected specs. Do NOT "fix" this by reverting the
`@unsafe` attributes in `mod.spl` — that would discard the capability-safety
work to suit a stale binary.
