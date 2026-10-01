# Authoritative C++ IDE/Lint Session

**Date:** 2026-09-03  
**Status:** focused implementation complete; broad compiler checks remain separate

## Implemented

- A retained `clangd` process lifecycle bound to an exact `compile_commands.json` selection.
- One revision-scoped C++ analysis ticket with idempotent cancellation and supersession.
- `clang-tidy` execution through the existing bounded structured worker.
- A publication gate rejecting cancelled, superseded, stale-revision, and digest-mismatched results.
- A combined receipt containing exact compile-configuration, clangd toolchain/build, and clang-tidy toolchain/build fingerprints.
- Explicit `Incomplete`/failed admission when the translation unit has no exact compile command.

## Architecture

The provider keeps Clang internals private. KPF-visible state is limited to immutable identities, revisions, digests, diagnostics, and receipts. `clangd` remains a retained IDE worker while `clang-tidy` remains a bounded batch worker; neither private C++ API crosses the boundary.

## Focused evidence

- `test/01_unit/app/lint/provider/cpp/authoritative_session_spec.spl`
- `test/01_unit/app/lint/provider/cpp/fixtures/fake_clangd.shs`
- Existing structured lint fixture remains authoritative for normalized diagnostics and fixes.
