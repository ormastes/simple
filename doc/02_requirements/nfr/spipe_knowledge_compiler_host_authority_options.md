<!-- codex-research -->
# SPipe Knowledge Compiler — Host Authority Provider NFR Options

**Status:** Decision required; paired with feature options F1–F3
**Date:** 2026-08-27
**Scope:** Non-functional consequences of the P3 host-provider choice

## Evidence baseline

The architecture's `HostReplaceCurrentCapabilityV1` requires raw-pointer exact
conditional replacement, `(scopeBytes,generation)` fencing, `current` parent
fsync before visible success, and a closed `replaced | mismatch | SPK704 fatal`
response contract. Research §43.8 records that normal Node `fs` cannot prove
it; neither rename replacement nor an advisory/user-space lock is admissible.
These are constraints, not permission to construct a Node fallback. A native
candidate needs separate admission evidence rather than an assumed portable
filesystem equivalence.

## Option N1 — Authority-service NFR profile (pairs with F1)

**Security and trust.** Mutual/service identity, least-authority operation
capabilities, tenant/workspace isolation, replay protection, service audit
records, and fail-closed authentication are mandatory. The service must not
make a client-side cache or file pointer authoritative.

**Portability and availability.** Node may remain portable as a non-publisher;
the service deployment becomes a required availability dependency for P3.
Define RTO/RPO and quorum/split-brain prevention if replicated; an unavailable
service throws/rejects and must never permit stale local publication.

**Performance.** Establish measured local and remote P95/P99 publish/open
latency, queue/backpressure bounds, restart recovery time, and durable-write
throughput after a baseline. No performance target may permit acknowledgement
before the durable authority decision.

**Acceptance evidence.** Independent partition/crash/replay, authorization,
and latency/load tests prove one linearizable winner, bounded failure, and no
client-side publication fallback. Service unavailability must fail closed by
throwing/rejecting a host failure; it must never add a fourth successful or
`unavailable` result. If the current closed `HostReplaceFatalV1` algebra cannot
encode that failure, selecting F1 first requires an explicitly reviewed algebra
revision.

**Effort:** XL; service SLO/security review, deployment fixtures, and
fault-injection harnesses in addition to functional implementation.

## Option N2 — Native-provider NFR profile (pairs with F2)

**Security and trust.** The native boundary must be narrowly capability-bound,
input-validated, memory-safe, and unavailable rather than permissive on an
unrecognized host/filesystem. It must preserve exact raw-byte evidence and
never silently downgrade an errno/fence/durability result.

**Portability and availability.** Support is an explicit
OS/kernel/filesystem/version matrix. A platform not in the matrix has no P3
publication; feature detection is not proof of semantic equivalence.

**Performance.** Measure fsync/fence/conditional replacement cost by admitted
tuple under contention and recovery. The target is bounded behavior with exact
semantic parity, not an optimization that batches or elides durability.

**Acceptance evidence.** Per-tuple native stress/SIGKILL/errno fixtures and a
negative matrix prove no unsafe provider activation. Golden ABI tests prove
same request/response bytes and P3 recovery results on all admitted tuples.

**Effort:** L–XL per platform; recurring certification cost applies whenever
the native runtime, kernel, filesystem, or provider changes.

## Option N3 — Deferred-publication NFR profile (pairs with F3)

**Security and trust.** All mutable publication/read-authority paths must be
removed from reachable configuration and fail closed. Offline output is
untrusted/non-authoritative and cannot influence capability decisions.

**Portability and availability.** Offline parsing/search works on all baseline
hosts without a native/service provider. Published authority availability is
intentionally zero and must be reported accurately, never degraded to an
apparent successful view.

**Performance.** Retain bounded offline build/query budgets and measure them
separately; do not claim P3 latency, durability, or availability targets.

**Acceptance evidence.** Negative entry-point tests prove no P3 mutation,
authority open, MCP canonical projection, or materialization occurs without
an admitted provider. Offline repeatability tests prove namespacing and no
authority leakage.

**Effort:** M; gating/diagnostic/docs work now, with the selected provider's
full NFR effort deferred.

## Selection requested

Select the NFR profile corresponding to the chosen feature option (N1/F1,
N2/F2, or N3/F3). These are alternatives, not amendments to the existing final
NFR document.
