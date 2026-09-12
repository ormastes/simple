# Windows Full Bootstrap and Toolchain Suite — Non-Functional Requirements

## Selection

Selected option: **N1 — Release-Grade Provenance and Bounded Performance**.

## Requirements

- NFR-001: Every promoted artifact and receipt must use SHA-256 and bind the exact source, command, environment/toolchain, parent compiler, and immutable output generation.
- NFR-002: Bootstrap, checks, tests, and service probes must fail closed on missing receipts, stale hashes, unsupported commands, fallback attempts, absent rows, conflict markers, or ambiguous executable identity.
- NFR-003: Process stdout and stderr capture must be bounded to the repository's shared 4 MiB-per-stream policy while retaining head, tail, omitted-byte markers, exit status, and timeout classification.
- NFR-004: Each acceptance criterion is executed at most once against unchanged inputs; a failure permits no more than three distinct fix/verify cycles.
- NFR-005: MCP/LSP and applicable tool services must retain warm-startup time, representative request latency, and maximum RSS on realistic fixtures. Existing documented targets are binding; when none exists, a measured baseline and explicitly selected target are required before final verification.
- NFR-006: Phase outputs and caches must be isolated and immutable after admission; a subsequent phase consumes a content-addressed snapshot rather than `bin/simple`, a wrapper, raw source, or a mutable stage path.
- NFR-007: Local deployment must be generation-atomic and rollback must be compare-and-select protected, restoring the prior exact digest without mixed-generation files.
- NFR-008: Publication and self-review evidence must bind the exact head and expire or invalidate on source, policy, base, or receipt drift.
- NFR-009: Windows-native evidence must identify the actual host/toolchain and cannot be replaced by Linux cross-build, synthetic, stub, source-only, or stale-artifact evidence.
- NFR-010: Retained evidence must be sufficient for an independent reviewer to reproduce the command, identify the exact executable, verify hashes, and distinguish PASS, FAIL, unsupported, and blocked states.
- NFR-011: Set `SIMPLE_NATIVE_INCREMENTAL=1` for eligible builds and require `[native-incremental] N reused / M rebuilt` with `N > 0`; use stable phase-specific caches and never clear them merely to retry a failure.

## Traceability Source

These targets refine AC-2, AC-8 through AC-21, and AC-24 in `.spipe/windows_full_bootstrap_toolchain_suite/state.md` and the selected N1 option.
