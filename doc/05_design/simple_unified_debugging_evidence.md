<!-- codex-design -->
# Simple Unified Debugging and Evidence — Detail Design

**Status:** Implementation-ready contract design
**Date:** 2026-08-14

## Core data

- `DebugSessionId`: opaque, non-reusable identifier.
- `DebugSessionRecord`: owner adapter, lifecycle, target graph revision, exact
  build identity, policy snapshot, deadlines and active probe IDs.
- `DebugTargetGraphV1`: typed nodes/edges plus monotonic revision.
- `DebugCapabilityV1`: operation, support, verification, perturbation, reason,
  verifier/tool version and evidence reference.
- `DebugEventV1`: event ID, target, build/source/symbol identity, correlation
  IDs, clocks, privacy labels, typed domain payload and provenance.
- `DebugReceiptV1`: request/action identity, actor/session, policy decision,
  perturbation, before/after graph revision, outcome, execution-changed flag,
  evidence IDs and cleanup state.
- `DebugPolicyV1`: environment/role operation matrix, capture/redaction limits,
  TTL/rate/retention, allowed perturbation and mutation approval.

All persisted schemas include `schema_major` and `schema_minor`. Unknown major
versions fail; unknown additive minor fields are preserved where forwarding is
required.

## Service operations

`open`, `close` and `describe` manage sessions. Observe reads events/graph;
Inspect reads state/evidence; Control performs stopping or state transitions;
Probe applies/removes/lists typed probes; Profile captures bounded performance
evidence; Evidence exports/imports/normalizes/inspects bundles; Domain dispatch
requires a registered `(domain, major, command)` tuple.

Each mutating call follows validate → authorize → start receipt → owner dispatch
→ validate result → commit → finish receipt. Failure finalizes the receipt and
does not partially publish a new graph revision.

## Wire behavior

`DebugWireV1` frames include version, request/stream ID, session ID, operation,
deadline, build/policy context and bounded typed payload. Responses distinguish
unsupported, unavailable, blocked, denied, invalid, stale-build, timeout,
adapter-crashed and internal errors. Streams have explicit credit/backpressure.

## Adapter interface

Adapters implement lifecycle, capability verification, graph snapshot,
operation dispatch and cleanup. Existing debug/profile backends are wrapped;
their mutable values never escape. Domain normalizers implement a separate
pure interface so offline evidence parsing does not require target control.

Each adapter binds an existing backend resource handle to `DebugSessionId`.
It must delegate mechanics to the landed owner: DAP target sessions, MCP DAP
bridge, mcpgdb GDB/LLDB runners, remote backend catalog, TRACE32 session/window/
action tools, OpenOCD/GDB-RSP/JTAG clients, or DbgEng. It must not duplicate
their transport, target-selection catalog, process supervisor, window access,
or dump parser. The adapter adds policy classification, exact-build binding,
target graph projection and outcome receipts around those calls.

The migration order is MCP DAP lifecycle, mcpgdb persisted resources, TRACE32
registry resources, then legacy coordinator retirement. `app/mcp/dap_types.spl`
is a compatibility copy to remove or convert from the canonical remote session
model; it is not a new contract source.

## Evidence bundle

The writer stages content, hashes every artifact, writes normalized references,
then atomically publishes `manifest.sdn` last. Import validates paths, sizes,
digests, schema versions, build/symbol compatibility and redaction policy.
Unknown raw formats remain retained and inspectable as opaque artifacts.

## Doctor

Doctor loads a profile, enumerates configured adapters, performs bounded
reachability/version/privilege and harmless verification checks, and emits a
stable matrix. It never upgrades a fixture result to live. Exit is success only
when profile-required rows meet their declared verification minimum; optional
blocked rows remain in output.

## First adapters

- Interpreter: structured frames/scopes/values, pure evaluation,
  tasks/actors/queues, semantic breakpoints and replay evidence.
- Simple SQLite/PureDatabase: the landed first slice executes a real
  parameterized query through the canonical pure-Simple engine and emits a
  sanitized statement digest, bind types, causality, monotonic timing, row
  count, and truthful table-scan plan. Host C SQLite remains a later explicit
  adapter for `sqlite3_trace_v2`, EQP/EXPLAIN, optional controlled ANALYZE,
  scan status, waits/errors/WAL/transaction events; it must not replace the
  PureDatabase owner or silently claim those facilities for it.
- Browser: CDP target discovery/auto-attach, source maps, Wasm DWARF,
  `BoundaryFrameV1`, redacted DOM/network evidence.
- Embedded: retained/custom dumps, event ring, GDB remote/OpenOCD/T32 bridges,
  JTAG/DMI/OBS reuse, RTOS task/ISR/queue nodes and source binding.

## Security and cleanup

Normalized payloads pass typed redactors before persistence. Raw sensitive
artifacts are separately classified, encrypted/access-controlled by the owning
environment, and never embedded in logs. Probe TTL is enforced server-side.
Close, timeout, adapter crash and client loss all schedule idempotent cleanup
and finalize receipts.

## Debug completion and knowledge accounting

Closure records the defect, root-cause owner, evidence, exact reproducer, tests,
cleanup, provider token fields or `unavailable`, comparable cohort average and
ratio. The system asks whether a reusable debugging fact, tool limitation,
failure signature or cheaper observation was learned. Ratio `> 2.0` blocks
closure until a knowledge/skill/tool link exists. Missing token data is visible
but never guessed or treated as zero.

## Error handling

Public operations return typed `Result<T, DebugErrorV1>`. Adapter errors retain
domain details as bounded evidence references, not unbounded messages. Stale
build or graph revisions require refresh; policy denial is not retryable without
changed authority; timeouts trigger cleanup and uncertain-state labeling.
