# LLM Build Progress Surface Design

`BuildProgressSnapshot` is a fixed schema with a bounded current-file list. Text fields use percent escaping. `publish_build_progress` validates the record, reads the prior bounded snapshot, enforces writer/sequence monotonicity, and calls the runtime atomic-write primitive. `log_build_progress` computes remaining count, observed rate, ETA, terminal state, and link projection from its existing arguments.

Configuration:

- `SIMPLE_WORKTREE_STORAGE_ROOT`: centralized authority;
- `SIMPLE_BUILD_PROGRESS_SNAPSHOT`: exact snapshot path;
- `SIMPLE_BUILD_ID`: current writer identity;
- `SIMPLE_BUILD_PROGRESS_EVENTS`: append-only evidence path;
- `SIMPLE_BUILD_RECEIPT_PATH`: optional authoritative receipt.

Bootstrap defaults the snapshot to `.simple/storage/build/progress/current.sdn` beneath the repository unless the centralized worktree root is explicitly supplied. Readers use the same resolved variables.

Failures to publish progress do not alter compilation semantics. They remain observable through absence/staleness and the detailed event stream; build correctness never depends on dashboard availability.

