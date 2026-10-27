# SCV Restore Specification

This manual describes the executable scenarios in
`test/03_system/app/scv/feature/scv_restore_spec.spl`.

**Status:** authored; runtime execution and canonical doc generation are
**NOT_RUN** because this worktree has no `bin/simple` or release runtime.

## Purpose and scope

The scenarios cover operation-view restore behavior and the read-only
`restore-op --check <op>` preflight. The preflight validates a selected
operation's view, commit, tree rows, reconstructed raw file bytes and bookmark
rows. It checks for a pending snapshot WAL, confirms that current HEAD,
workspace, bookmarks and status index agree, and refuses dirty tracked files
and collisions with untracked target paths.

The check makes no changes and does not repair or replay WAL state. It is an
advisory inspection only: it does not authorize a later mutation or claim
concurrent snapshot safety. Successful output states
`mutation=unsupported`, `recovery=unsupported`, and
`atomicity=unclaimed`, plus `operation_id_integrity=unavailable` because SCV's
current operation IDs are not hashes of their payloads. The tracked-file
inspection limit for trees, status, WAL, target files and tracked worktree
files is 16 MiB. It also caps each target/current view at 10,000 rows and 64 MiB of raw
bytes, direct operation/commit parents at 32, and bookmarks at 256. Small
records are limited to 256 KiB.
Immutable file/chunk reconstruction uses the current SCV structural storage
owner after validating the tree's file and chunk reference prefixes. The
preflight assumes the repository's `.scv` object-store directories are not
replaced adversarially during inspection; the check has no cross-process
mutation lease.

The legacy `restore-op <op>` mutator remains sequential. It has no complete
working-tree WAL or whole-view atomic publication protocol and may move HEAD to
a historical operation. These scenarios do not claim to close those gaps.

## Preconditions

- Each fixture creates its own temporary repository and immutable SCV objects.
- Worktree inspection uses the bounded no-follow read owner; unsupported host
  containment or oversized tracked files fail closed.
- A pending WAL is left untouched for normal recovery tooling or an operator
  to resolve.

## Scenarios

### REQ-004: legacy operation-view restore

**Restores exact files and deletes tracked paths absent from the target tree.**
The fixture snapshots a base file, adds and snapshots a second file, then
restores the first operation. It checks that the later tracked file is removed
and the base bytes are present.

### REQ-004: read-only restore preflight

**Validates a complete target without changing repository or worktree bytes.**
The fixture saves a target and a later view, captures HEAD, workspace,
bookmarks, status index, and worktree bytes, then verifies that the preflight
reports advisory-only status and every captured subject is unchanged.

**Rejects deleting a dirty tracked file.** A tracked file absent from the
target is edited after the last snapshot. The preflight reports the conflicting
path and preserves the unsaved bytes.

**Rejects overwriting a changed-size tracked file.** A tracked file still
present in the target is edited to different bytes and length. The preflight
reports a dirty tracked path and preserves those bytes.

**Rejects an untracked destination collision.** An untracked file occupies a
path present in the target. The preflight reports the path and leaves its bytes
untouched.

**Refuses unresolved WAL without replay.** The fixture creates an incomplete
snapshot WAL record. The preflight reports pending recovery and leaves HEAD,
workspace, and WAL bytes unchanged.

**Rejects current HEAD/workspace drift.** The fixture alters workspace metadata
without changing HEAD. The preflight reports the mismatch and does not repair
either value.

**Rejects a missing operation.** An absent operation ID returns an error while
HEAD remains unchanged.

**Rejects a missing target chunk.** After a target chunk is removed, the
preflight reports the missing immutable object and leaves worktree bytes and
HEAD unchanged.

**Rejects conflicting target path shapes.** The fixture constructs verified
file objects for both `a` and `a/b`. The preflight rejects the file/descendant
collision before reporting any restore plan.

**Rejects a missing target below a symlink parent.** The fixture places a
symlinked directory in the repository and creates a target path beneath it.
The preflight resolves the existing ancestor, rejects its noncanonical
in-root spelling, and neither reads nor creates the external leaf.

## Running and interpreting the evidence

Run the system spec with the admitted pure-Simple runtime and regenerate this
manual through SPipe docgen before claiming executable PASS or generated-manual
quality. A source-level assertion is not a runtime result. Errors from the
preflight mean no mutation was attempted; users must separately decide how to
resolve dirty data, collisions, or pending WAL state.
