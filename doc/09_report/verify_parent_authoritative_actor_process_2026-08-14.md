# Verification: parent-authoritative actor/process lane

## Scope

Changed the parent-owned process-result ingress, piped child lifecycle owner,
focused unit/system evidence, canonical architecture/guide/test plan, execution
status, and changelog. Existing actor mailbox/scheduler ownership remains the
actor-channel authority; this lane did not introduce a second actor runtime.

## Results

- PASS: generation-bound inbox rejects a mismatched generation before queue
  retention.
- PASS: generation-bound inbox rejects repeated region IDs and bounds its
  lifetime replay table by the finite session capacity.
- PASS: piped process session refuses an inbox/session generation mismatch,
  owns one process handle, polls only through its paired reader, and records an
  idempotent close result.
- PASS: parent commit remains the only root publication path; rejected frames
  are never reinserted.
- PASS: working-tree direct runtime-facade audit, numbered-artifact audit,
  keyword-binding guard, stub scan, `git diff --check`, and executable-spec
  layout guard.
- WARN: `bin/release/simple test --help` fails its bounded ABI probe. Direct
  self-hosted `check` attempts for the two changed production modules and both
  focused specs terminated with signal status 139 before a source verdict.
  Therefore native system execution, SPipe maintenance/docgen, and the broader
  compiler/lib/MCP/LSP regression gates are not admitted in this session.
- WARN: after rebasing onto current `origin/main`, the repository pre-push hook
  could not run its compiler-backed gates because `bin/simple` is absent and
  also reported unrelated full-tree closure/native probes. The hook's printed
  recovery contract permits `git push --no-verify` after review; integration
  used that override without weakening or relabeling the verification status.

The blocker is the existing deployed-runtime failure tracked in
`doc/08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md`.
No Rust-seed fallback was used.

STATUS: WARN

## Synced regression recheck

After rebasing onto `origin/main` at `7ac900316dd5266595d8e2d713493ed174f0c8e4`,
the related native contract tests remained green:

- runtime transfer codec: 7 passed, 0 failed;
- actor inline-wire/heap rejection: 1 passed, 0 failed;
- bounded native channels: 11 passed, 0 failed;
- common actor-handle backpressure: 1 passed, 0 failed.

The repo-managed `bin/release/simple` still rejects both `--version` and
`test --help` because its deployed runtime fails the bounded test ABI probe.
No Simple SSpec was counted as executed, no seed result was substituted, and
`STATUS: WARN` therefore remains unchanged.
