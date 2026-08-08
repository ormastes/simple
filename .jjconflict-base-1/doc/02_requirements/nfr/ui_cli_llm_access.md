<!-- codex-research -->
# UI CLI LLM Access — NFR Requirements

**Date:** 2026-07-11
**Status:** Selected NFRs
**Selected options:** N1-A, N2-A, N3-A

## Performance and resources

- NFR-UCLA-001: On a warm representative fixture containing 100 windows/surfaces and 1,000 semantic nodes, list and snapshot operations shall meet p95 <= 100 ms.
- NFR-UCLA-002: Cached find and common action routing before backend execution shall meet p95 <= 20 ms on the same fixture.
- NFR-UCLA-003: The access CLI path shall add no more than 20 MiB maximum RSS over the representative warm fixture baseline.
- NFR-UCLA-004: Default recent history shall remain bounded at the existing 64 events unless an existing owner configures a smaller bound.
- NFR-UCLA-005: List, snapshot, find, serialization, and history hot paths shall not perform full-tree filesystem scans, source reparsing, subprocess execution, or one refresh/subprocess per listed window or node.

## Safety and reliability

- NFR-UCLA-006: List, snapshot, surface, find, and history shall be declared and implemented as read-only operations.
- NFR-UCLA-007: Every action shall re-resolve the target, verify advertised capability and current state, validate bounded input, use the owning adapter, enforce a timeout, and record a correlated result.
- NFR-UCLA-008: Destructive or prompt-crossing operations shall be eligible for explicit confirmation policy and shall never be silently approved by the common layer.
- NFR-UCLA-009: The implementation shall not silently fall back from semantic access to lower-confidence raw input or fabricated output.
- NFR-UCLA-010: Backend unavailability, stale/defunct targets, permission denial, unsupported actions, disabled/busy targets, interaction requirements, invalid input, and timeouts shall remain distinguishable.

## Compatibility and schema

- NFR-UCLA-011: Existing UI modes, observer commands, play commands, MCP/HTTP tools, persisted access behavior, and protocol version behavior shall remain compatible.
- NFR-UCLA-012: JSON field additions within a protocol version shall be optional/additive; changes to existing field meanings or types require a major protocol version.
- NFR-UCLA-013: JSON shall use UTF-8, unique object member names, deterministic documented array ordering, explicit bounds/truncation, and no dependency on object-member order.
- NFR-UCLA-014: `--json` success output shall contain only the documented payload on standard output; diagnostics shall use standard error; success shall exit 0 and failures shall exit nonzero with stable codes.

## Architecture and maintainability

- NFR-UCLA-015: App/UI/WM code shall use existing Simple facades and common owners; no new raw `rt_*`, direct env/process shortcut, backend field poke, or fixture-only bypass shall be added.
- NFR-UCLA-016: Production wrappers shall execute cached compiled artifacts rather than raw source entrypoints.
- NFR-UCLA-017: Command startup and request paths shall not add repeated full-tree scans, repeated source rereads, retry sleeps, or avoidable shell-outs.
- NFR-UCLA-021: The shared access grammar shall be data-only and dependency-light so T32, UI, and WM entry closures import no unrelated renderer, backend, or mutable host adapter.
- NFR-UCLA-022: UI CLI service calls shall default to loopback, use a finite selected timeout, reuse existing HTTP/client facades, and perform at most one request per operation plus the single post-action observation required by the action contract.

## Verification

- NFR-UCLA-018: Perf evidence shall record fixture size, warm/cold state, p50/p95, maximum RSS, command/backend, and output checksum or semantic count.
- NFR-UCLA-019: System evidence shall use real assertions, manual-facing `step()` calls, GUI/TUI captures where applicable, and no placeholder passes.
- NFR-UCLA-020: Final verification shall run focused unit/integration/system/perf evidence, direct runtime guards, dependency checks for changed entrypoints, generated-spec layout guard, documentation freshness checks, and highest-capability merged-result review exactly once after convergence.
