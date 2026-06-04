# SCV Local Research

Status: initial Codex research, 2026-05-14.

## Current Repository State

No `scv` source or SCV-specific specs exist in this checkout yet. The closest existing VCS work is:

- `doc/04_architecture/app/sj_vcs_service.md`: a Jujutsu/Git wrapper service that serializes existing VCS commands through `sj`.
- `src/app/vcs/git_wrapper.spl`: a compatibility wrapper translating some Git commands to `sj`.
- `src/app/vcs/__init__.spl`: re-exports the wrapper surface.
- `.jj/` exists at the repo root, so current project workflow already uses Jujutsu.

`sj` is not an internal object-store VCS. It is useful prior art for CLI ergonomics and jj-like workflow expectations, but `scv` should be a separate repository model.

## Reusable Simple Modules

Likely reuse points:

- File I/O: `src/lib/nogc_sync_mut/io/file_ops.spl` and `src/app/io/mod.spl`.
- Hashing: `src/os/crypto/sha256.spl` through pure Simple `sha256`.
- Compression: `src/lib/gc_async_mut/compress/` and any sync/no-GC equivalents found during implementation.
- Database/indexing: existing `std.nogc_sync_mut.database.*` modules.
- Atomic writes: `std.nogc_sync_mut.database.atomic.atomic_write`.
- CLI patterns: `src/app/*/main.spl` apps and `src/app/cli` dispatch.

## Existing VCS UX Lessons

`sj_vcs_service.md` shows a repo-local service model with:

- clear command lanes for mutating vs read-only operations,
- audit logs,
- daemon lifecycle controls,
- Git-mimic command compatibility,
- jj-native workflow assumptions.

For `scv`, reuse the UX lessons but avoid making `scv` a shell wrapper around jj/git. `scv` needs its own byte-exact object store and operation log.

## Platform Finding

The repo has broad architecture support across x86, ARM, and RISC-V. Existing docs and tests mention x86_64, x86_32, ARM64/ARM32, RISC-V 64, and RISC-V 32. Therefore `scv` should document x86-64 and ARM64 as primary developer targets, with RISC-V as a compatibility and portability target rather than the only target.

## Local Risks

- `file_read_text` in the hosted runtime has a same-path read cache; byte-exact SCV identity should avoid text reads and hash bytes directly.
- Existing `sj` documentation may confuse readers unless `scv` docs explicitly distinguish wrapper-service VCS UX from a new content-addressed VCS.
- Full Tree-sitter integration may require native/WASM runtime work outside a first raw-byte MVP.

## Recommendation

Start with `src/lib/scv/` and `src/app/scv/`, not `src/app/vcs/`. Keep MVP step 1 and 2 independent of parser runtimes:

1. byte object store,
2. tree/commit/operation metadata,
3. working-copy scan and status,
4. line/binary fallback view,
5. restore and operation-log undo.
