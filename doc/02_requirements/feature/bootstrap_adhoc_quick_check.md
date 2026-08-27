# Bootstrap ad-hoc quick check requirements

- REQ-ADHOC-001: Operate only in the invoking worktree and write artifacts
  below an explicit worktree-local output root.
- REQ-ADHOC-002: Classify compiler changes as frontend, HIR, MIR, backend, or
  full-bootstrap-required; requested lanes may widen but never narrow.
- REQ-ADHOC-003: Reject common ABI, interpreter, loader, MDSOC, weaving,
  deleted, missing, non-compiler, and non-POSIX-path changes.
- REQ-ADHOC-004: Reject Rust bootstrap-seed identity.
- REQ-ADHOC-005: Compile and execute a positive fixture and require its exact
  lane marker.
- REQ-ADHOC-006: Require a negative fixture to fail compilation with a caller
  supplied expected diagnostic substring and no emitted artifact.
- REQ-ADHOC-007: Bind compiler, fixtures, changed files, backend, lane, and
  worker count into a content-addressed local session receipt.
- REQ-ADHOC-008: Every receipt states `release_admissible=false` and
  `full_stage4_required=true`; the tool never writes `bin/simple`.
