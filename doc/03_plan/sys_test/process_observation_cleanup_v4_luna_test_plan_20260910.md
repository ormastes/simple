# G5 Process Observation V4 cleanup test handoff (Luna)

State: design-frozen test contract; common V4 and the production facade are
integrated, but production remains NO-GO pending a qualified host fixture and
native Simple evidence. Freeze artifact:
`/tmp/g5-process-observation-v4-cleanup-freeze-20260910.md` (SHA256
`5ec8e9c237fa98d93a2f746264b6fda4cff04143f0012b73d2fcec88d926a26e`).

## Interface map

| Interface | Test contract |
|---|---|
| `ProcessObservationPacketKindV4` kinds 4/5 | CleanupFrozen and CleanupAck are distinct from ordinary Frozen/Ack; unknown kinds reject. |
| `freeze_process_observation_cleanup_receipt_v4` | Direct DTO construction cannot bypass cleanup status/phase, ticket, stream, failure, reap, or digest invariants. |
| `ProcessObservationLeaseV4.acknowledge_cleanup` | Exact ticket/request/digest/kind match is required; successful host Ack precedes deactivation. Wrong digest, wrong kind, duplicate, and cross-owner responses preserve ownership. |
| `rt_process_observation_v4_*` facade | Pinned start/poll/cancel/collect/ack preserve CleanupPending authority and absolute deadlines through startup failure, cleanup, freeze, and ack. |
| Frozen digest | `POV4FRZ\\0` + canonical request + 64 LE words + complete stdout/stderr; changing one field changes the digest. |

## Executable artifact

`test/02_integration/lib/io/process_observation_cleanup_v4_spec.spl` declares
the frozen Luna helper names and visible manual steps. Helpers that acquire
wires/leases or inspect live ownership and child cleanup fail explicitly with
`MissingEvidence`; no synthetic wire, handle, or shadow ownership boolean is a
pass. Pure receipt, snapshot, and deadline assertions use the integrated common
DTO. Replace host helpers only with owner-issued production-boundary fixtures.

The required matrix is C01–C25 from the freeze artifact. The first implementation
slice targets C02/C03/C18/C19/C23, including the critical wrong-digest
regression: a decodable Rejected response must leave the lease active. Extend
the same spec with deterministic fault-injected C/H rows; live H/N rows stay
separate and unqualified until a real Linux child/pin/native Simple receipt is
available.

This executable file remains a scenario skeleton: its host-acquisition
fail-fast fixtures mean zero executed live branch coverage. It must not be
reported as C02/C03/C18/C19/C23 coverage until the qualified host boundary and
real assertions execute.

## Sol review guide

Check exact helper names, five visible step strings, builtin matchers, and
production facade calls. Require RED helpers to use `fail(...)`, never a no-op.
Review CleanupPending phase stability, Pending versus Failed exec evidence,
ESRCH child-gone semantics, absolute deadline/EINTR behavior, and exact
CleanupAck ticket+digest matching. Ticket assertions use the frozen five-word
`[4, request_hi, request_lo, ticket_hi, ticket_lo]` form and ownership oracle;
the lease is never treated as a shadow authority. Do not count selfchecks, source scans,
interpreter runs, or Rust seed runs as N coverage.

## Astra final review guide

Review separate >=95% measured branch reports for common, facade, host, and
critical ownership/release/deadline/signal/ack decisions at 100%. Accept only
identical source/runtime/spec hashes, complete C01–C25 mapping, and generated
manuals with zero stubs. Keep physical provider rows `MissingEvidence` until
real descriptor/pin, child-reap, process-kill/reopen, and native Simple
evidence exists.
