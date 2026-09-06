<!-- codex-design -->
# M5 Hermetic Portable Qualification Architecture

## Decision

Focused M5 portable qualification executes only from a read-only, explicit
three-file snapshot: the hermetic driver, portable checker, and M5 release
owner. The driver first copies and re-executes itself, then inventories and
copies the remaining closure. Worktree scripts are never executed after the
snapshot boundary.

## Integrity Boundary

The evidence generation binds ordered relative paths, byte sizes, per-file
SHA-256 digests, and the aggregate inventory digest. Source inventories are
compared before copying, immediately before execution, and after execution.
Snapshot inventories are compared before and after execution. Missing files,
symlinks, copy races, source drift, snapshot drift, or checker failure reject
the run while retaining digest-bound, read-only evidence.

## Isolation

The checker receives a minimal environment and system-only `PATH`; `HOME` and
`TMPDIR` point inside the evidence directory, and its working directory is the
snapshot root. The snapshot and retained evidence are read-only. The
wrapper has no commit, deployment, signing-authority, or native-admission
operation. Its output is portable structural evidence under `build/` only.

## Consequences

- Concurrent worktree edits cannot alter executed M5 script bytes.
- A run whose source lineage changes anywhere across its boundary fails closed.
- Adding a new checker dependency requires an explicit inventory-schema change.
- Native M5 and Apple signing/notary qualification remain separate gates.
