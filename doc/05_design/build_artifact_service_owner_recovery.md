# Parent-authoritative build owner recovery

Status: proposed recovery design for the user-selected no-duplicate-build and
conditional-progress requirements. The service completion hardening is a narrow
implemented prerequisite; recovery APIs below are not implemented or admitted.

## Authority and transitions

The build/test parent owns one serialized service state per admitted immutable
action key. Workers receive opaque leases; they cannot requeue themselves or
rewrite the parent's queue. A key binds source generation, compiler/parser,
configuration/target, observed dependencies and semantic invalidators.

Extend the runner's actual spawn owner with an owner-instance receipt containing
the process handle/start identity, action key, lease generation, runner session
and invocation nonce. A PID alone is insufficient. The trusted provider emits a
death receipt only after the original instance has exited and its contained
children/locks are closed. Heartbeat timeout is a request to inspect or cancel
that instance; it is not a death receipt.

The parent applies `leased(g, owner) -> queued(g+1)` only when the death receipt
matches its still-current lease, no completed result has been published, and
all execution ownership has ended. Reserve release and the generation advance
are one authoritative transition. A new claim consumes only the new generation.
Old worker completions are ignored without changing the current owner's state.
Publication independently checks action, generation, snapshot and complete CAS
closure. Crashes between artifact write and publication leave unreachable CAS
content; they do not authorize a second successful publication.

If parent state is persisted, journal the fence/requeue transition durably before
granting the new claim. On parent restart, reconstruct the exact generation and
reconcile provider instances before executing work. A stale heartbeat or an
unverifiable owner leaves the request blocked/cancelled with a diagnostic.

## Parse reuse and lifetime

One miss owner parses the immutable input and retains an owned complete flat
frame or promoted rich AST, plus its parser/codec/target identities. TLDR/HIR
production and later compilation consume that retained result. OS-owned locks
release on real process death; a reader rechecks the published cache after
acquiring the miss lock. No raw index into mutable flat-pool globals survives
reset. Failed parse, corruption, eviction or generation change permits a new
parse; successful retained generations do not.

Interpreter/test sharing needs separate memory admission. Enabling the existing
unbounded serialization path globally is not this design: its recorded cold
RSS regression is 8.77 GB versus 5.22 GB warm. Measure and bound retained bytes,
promotion lifetime and eviction with the same correctness/parse-count checks.

## Executable acceptance

Exercise the actual runner owner and OS process provider, not only the pure
service DTOs. Test death before parse, during parse, after cache write and before
publication. In every case require at most one live worker for a key, stale
completion rejection, resource release and a successful single retry. Test
reused PID, wrong session/nonce, stale generation, timeout without death,
parent restart with a torn journal and a completed result before recovery.

Safety needs serialized owner transitions and a correctly functioning process
provider. Liveness additionally assumes finite dependency work, fair scheduling,
eventual sufficient resources/storage, eventual provider completion and eventual
death detection. Continuous churn or repeated worker death is not covered by an
unconditional progress theorem.

Source replay/specs: `test/00_formal_verification/compiler/`
`build_cache_service_refinement_spec.spl` and `build_cache_parse_reuse_spec.spl`.
Those narrower specs do not yet satisfy the live runner recovery scenarios.

## 2026-10-18 bounded production transition (unqualified)

`compiler.driver.action_graph.artifact_owner_recovery` now provides
`demand_artifact_recover_owner_v1`. Its input route, `GroupProcessOwnerV1` and
`GroupedActionLeaseV1` are trusted retained parent state, not worker submissions.
The service lease owner is the full broker launch identity digest; snapshot and
compatibility identities must equal the broker binding's snapshot/cache digests.
Existing routes with free-form owner/compatibility labels are not automatically
eligible for this recovery protocol.

Before collecting anything, the function checks canonical launch identity,
current service lease and state, successor identity/generation, and coordinator
snapshot/token/running state. It calls the existing
`group_process_collect_reap_v1`, which verifies durable terminal leader/tree
evidence and persists an exact lease-bound receipt. An error leaves the supplied
route unchanged. A successful return contains both staged owner transitions:
service queued with its retired lease retained as a generation fence, coordinator
pending with zero reservation, and the successor identity/generation. The parent
installs that returned value once. This is serialized value-state transfer; it
does not make independent concurrent route copies authoritative.

The service refuses queued claims at or below the retained lease generation.
The next admitted lease carries the `owner-recovered` entry marker. After this
marker, bridge completion requires the explicit publication lease retained from
dispatch. Missing, cancelled or mismatched owner/token/action/generation fails
before either coordinator or service publication. Ordinary unrecovered callers
retain the existing optional-lease API behavior. Callers must never synthesize
the publication lease by looking up current state when a result arrives.

The finite claim-only dead-owner fixed-point counterexample remains valid:
claiming with a newer epoch alone still cannot steal a live or unknown owner.
Recovery now has a separate explicit proof-consuming transition. Production
runner spawn/dispatch integration and parent-journal recovery remain unimplemented;
this API does not silently wire them or certify any of the nine feature groups.

New real-API protocol scenarios:
`test/03_system/compiler/incremental/artifact_owner_recovery_spec.spl` and its
mirrored manual. They use filesystem broker-receipt fixtures and are UNRUN;
they are not real OS death or descendant cleanup qualification.
