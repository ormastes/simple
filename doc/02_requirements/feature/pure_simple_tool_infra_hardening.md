# Pure-Simple tool and infrastructure hardening requirements

Selected: Feature option C on 2026-07-16.

- REQ-001: Production launchers must reject a Rust bootstrap seed or debug
  binary presented as the deployed `simple` runtime.
- REQ-002: Deployment must validate the candidate, swap atomically, retain a
  rollback candidate until post-swap probes pass, and restore on failure.
- REQ-003: The test runner must never turn a nonzero child exit, assertion
  failure, internal error, timeout, or partially executed spec into success.
- REQ-004: Multiple sibling top-level `describe` blocks must all execute, and
  authored/executed example-count disagreement must fail closed.
- REQ-005: A test launched from a daemon-owned child must bypass the same
  single-threaded daemon so nested tests cannot self-deadlock.
- REQ-006: Test outcomes must expose stable classes for pass, assertion failure,
  empty discovery, usage error, internal error, and timeout/resource failure.
- REQ-007: Duplicate-check must discover and read files through Simple IO APIs;
  CLI paths, excludes, and generated scripts must never enter a shell command.
- REQ-008: Duplicate-check must retain one canonical benchmark/qualification
  spec with real assertions and no placeholder duplicate copy.
- REQ-009: Lint annotations must use the compiler's canonical parser, preserve
  scope, and correctly support multiple lint names.
- REQ-010: Lint, format, and fix must have one behavior owner; production
  wrappers may adapt arguments but must not execute raw source workers.
- REQ-011: CLI dispatch inventory and coverage must derive from the canonical
  command table and describe fail-closed behavior accurately.
- REQ-012: MCP and LSP launchers/installers on Linux and Windows must prefer a
  validated cached native pure-Simple artifact and must not silently route
  production work through a Rust seed, debug binary, or raw source entrypoint.
- REQ-013: Test-daemon run/clean/status/stop and cache invalidation behavior must
  have production-path qualification evidence.
- REQ-014: Checker global flags and `gen-lean` dispatch must terminate within
  their deadlines and must not recurse into themselves.
- REQ-015: The feature must provide an executable SPipe qualification spec,
  generated manual, implementation mapping, and current operator/developer guide.
