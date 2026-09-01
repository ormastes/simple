# VFS Mutation Receipt Owner V1 — Agent Tasks

## Phase 1 (this lane)

- Owner: Codex mutation-receipt lane
- Implement bounded frozen-value task/OFD/object contracts.
- Implement bounded O(1) grant/receipt owner and exact event oracle.
- Add package-level static SSpec coverage.
- Final reviewer: independent Codex sidecar, static review only.

## Deferred lanes (active, not excluded)

- VFS integration owner: derive current task/OFD/object identities and route
  FAT32, DBFS, and NVFS create/write/truncate/rename/fsync/close operations.
- Scheduler owner: publish non-forgeable current `TaskExecutionInstanceV1` and
  increment exec generation atomically at exec.
- Toolchain provenance owner: assemble ordered receipts plus stable snapshot;
  do not infer causality from path, stdout, or process exit.
- System-test owner: run cross-filesystem alias/fork/crash/indeterminate and
  Clang/LLD hello-world scenarios when runtime wiring exists.
- Merge owner: SimpleOS filesystem maintainer.
- Final reviewer: highest-capability independent reviewer after integration.

No phase-1 artifact closes these deferred tasks or proves filesystem output.
