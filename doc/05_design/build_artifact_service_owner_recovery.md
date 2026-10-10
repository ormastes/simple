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
