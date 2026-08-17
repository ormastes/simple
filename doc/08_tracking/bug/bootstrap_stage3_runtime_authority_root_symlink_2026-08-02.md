# Bootstrap Stage 3 runtime authority root symlink

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

- Claimed: 2026-08-02
- Owner: Codex `stage4_bootstrap_close` Rust/bootstrap lane
- State: fixed and regression-covered

## Reproduction

In a secondary worktree, make `src/compiler_rust/target/bootstrap` a symlink to
the complete physical Rust bootstrap directory in the main worktree, then run
the full-bootstrap admission path. It exits before private admission with:

```text
error: could not snapshot Rust runtime authority
```

The target directory is complete. The failure occurs because
`bootstrap_stage3_directory_snapshot` deliberately rejects a symlink at its
root, and the bootstrap driver passes the lexical worktree path without first
binding it to the physical directory.

## Intended fix

Resolve the runtime authority root to a physical directory before snapshot and
copy admission. Continue rejecting broken roots and every symlink contained
inside the authority tree. Cover physical, root-symlink, broken-root, and
interior-symlink cases in an isolated executable regression.

## Resolution

The driver now binds the lexical worktree path through
`bootstrap_stage3_physical_directory` before taking or copying authority
snapshots. The snapshot implementation itself remains fail-closed for a
symlinked root and for interior symlinks.

Validation (run once):

```text
bootstrap_stage3_runtime_authority_root=true
```
