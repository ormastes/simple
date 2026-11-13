# `dir_create_all`/`dir_exists`/`dir_remove` same-signature cross-module collision silently swaps bodies

- **Date:** 2026-11-12
- **Status:** OPEN (root-caused; blocked on codebase-wide collision debt, owner decision 2026-11-09)
- **Severity:** High — silently wrong answers in any closure that co-compiles the colliding set; makes importing specs vacuous
- **Area:** `src/lib/nogc_sync_mut/io/dir_ops.spl`, `src/lib/nogc_sync_mut/io_runtime.spl`, `src/lib/nogc_sync_mut/sffi/io.spl` (and the `mod_stub` variants)

## Repro

`test/02_integration/app/release/session_lifecycle_spec.spl` (also
`candidate_authority_spec.spl`, `convergence_git_spec.spl`,
`session_authority_spec.spl`, `windows_local_artifacts_it_spec.spl`):

```bash
./bin/simple.exe test test/02_integration/app/release/session_lifecycle_spec.spl --timeout 300
# → 1 example, 1 failure: "expected false to equal true" on the very first
#   dir_create_all(primary + "/.spipe/policy") assertion.
```

The identical preamble run standalone (same imports of `app.io.mod`, same
`get_temp_dir()`-anchored path) succeeds — `dir_create_all=true`,
`file_atomic_write=true`, `git init=0`. Only the spec's larger co-compiled
closure fails.

With the compiler's own diagnostic:

```bash
SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 ./bin/simple.exe test \
  test/02_integration/app/release/session_lifecycle_spec.spl --timeout 300
```

the compiler prints, for `dir_create_all`:

> public function `dir_create_all` has 3 co-compiled definitions across 3
> modules with the SAME signature ((text)->bool) — one silently wins and the
> rest are discarded. Because the signatures agree, no type/arity error and no
> ambiguity fallback can fire, so a call resolves to a different module's body
> than the one it imported: a silent wrong answer, and the shape that makes an
> importing spec vacuous.
> Defined in: src\lib\nogc_sync_mut\io\dir_ops.spl,
> src\lib\nogc_sync_mut\io_runtime.spl, src\lib\nogc_sync_mut\sffi\io.spl

The same warning fires for `dir_exists` and `dir_remove` (3 definitions each).

## Root cause

Eight definitions of `dir_create_all` exist across `src/app/io/dir_ops.spl`,
`src/app/io/minimal_runtime_ops.spl`, `src/app/io/mod_stub.spl`,
`src/lib/gc_async_mut/io/mod_stub.spl`,
`src/lib/nogc_async_mut/io/mod_stub.spl`,
`src/lib/nogc_sync_mut/io/dir_ops.spl`,
`src/lib/nogc_sync_mut/io_runtime.spl`, `src/lib/nogc_sync_mut/sffi/io.spl`.
In the release-spec closure, the winner's body returns `false` for a
perfectly valid host-temp path, so the fixture cannot be built. The spec-side
`/tmp` → `get_temp_dir()` anchoring was fixed in this lane
(work/product-queue-p1-20261112) but cannot make the spec green while the
collision remains — no spec-side import choice changes which body executes.

## Affected queue specs (phase-2 product lane p1)

- `test/02_integration/app/release/session_lifecycle_spec.spl`
- `test/02_integration/app/release/session_authority_spec.spl`
- `test/02_integration/app/release/candidate_authority_spec.spl`
- `test/02_integration/app/release/convergence_git_spec.spl`
- `test/02_integration/app/release/windows_local_artifacts_it_spec.spl`
- `test/02_integration/app/release/release_cli_spec.spl` (same closure family)

## Fix direction

Per the compiler warning and owner decision 2026-11-09: rename the colliding
helpers to unique names (e.g. `io_runtime_dir_create_all`,
`sffi_dir_create_all`) and update the facade re-exports, or make the facade
modules the single definition point and turn the others into `export use`
aliases. This is a codebase-wide debt item, not a per-spec fix.
