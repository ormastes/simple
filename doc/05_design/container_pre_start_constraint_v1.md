# Restrictive checks within existing signed Host execution

Status: AUTHORED_NOT_RUN; native/compiler/spec qualification is absent. No new
admission, journal, executor, service, process supervisor or Caret main route.

`ContainerPreStartConstraintV1` is common DATA. It binds the exact signed request
digest, canonical actual Host scope and provider generation, immutable requested
image reference/config digest, effective argv/workdir/user, ordered environment
digest, complete allowed mount vector and optional actual read-only-root fact.
The common pure comparison accepts diagnostic DTOs only as DATA. Only the Host
effect path invokes the actual configuration producer and consumes its result.

Original public entry signatures remain compatibility wrappers selecting no
additional restriction. New constrained entries deep-copy arrays before refresh
callbacks or effects, validate the restriction after signed admission preparation
and before capacity execution begins, then retain it in the existing private
Windows progress state. Neither matching DATA nor a callback can supply a grant.

The synchronous Linux/Windows route checks its own actual create return, stores
the exact creation intent through the same writer, observes actual configuration,
and refreshes existing admission before start. The Windows cooperative path stores
that same native runtime identity in its canonical state and inserts a
`constraint` stage after completed create/durable intent and before `start`.
The new stage has no active native command. It invokes the fixed common
configuration producer, returns its updated owner, and advances to start only on
an exact match. Unknown/mismatch advances to inspection/error recording. The
existing charge, created container owner, durable intent and native cleanup are
retained. Cancellation while a native command remains uses the existing owner.

## Fresh birth source audit

Linux `oci_runtime_v1.spl` has exactly two successful `_ok("create",...)` producer
branches: the idempotent existing workload at 972–980 emits an empty command;
the current actual create path at 1013–1049 accepts the successful owned native
command, validates its returned native ID, retains identity and writes created
intent before returning that actual create command. Saved-intent recovery at
983–998 returns the `recover` operation; failure recovery at 1970–1977 also returns
the actual recover result, whose successful operation is `recover` at 1419.
The constrained path therefore requires the current private Host→common owner
create return to have operation/create-command `create`, nonempty program and
exact created identity. An idempotent or recovered created phase is refused.
No caller RuntimeOperation constructor feeds this decision.

Windows `docker_runtime_v1.spl` 589–596 rejects create unless its actual record is
prepared with `create_attempted=false`. The current native-create transaction sets
`create_attempted=true` and retains `effect_command` at 658–670; actual returned ID
sets `native_birth_retained` at 672–684. Only after engine/configuration inspection
does completion at 694–704 return the retained effect command. Failed/uncertain
progress remains failure or retains the actual native command owner; existing
record/recovery cannot supply a current fresh create result. Both finite and
cooperative routes use this reducer. Scripted fixture modes remain tests, never
native qualification.

These observations do not exclude a privileged external engine administrator,
replace trusted runtime namespace custody, prove writable-layer reuse safe, or
authorize another session/history/workspace. Tasks require genuine signed
admission and the protected first-start topology. Native qualification remains
required. No caller StartedAt string or freshness boolean is introduced.

## Forwarding and source scope

`host_service_domain_effect_constrained_turn_v3` forwards synchronous Linux and
Windows requests. Windows opaque root adds `execute_constrained_v3` while
`execute_v3` delegates to it, retaining readiness/owner-reconciliation logic once.
`host_service_execution_begin_constrained_v4` forwards the Windows cooperative
route; original service begin delegates with no restriction. Linux uses the
existing finite effect-worker route; no new cooperative scheduler is introduced.

Current-base preimages for the four existing orchestration files are retained in
`/tmp/caret-prestart-preimages-20261115`. Collector6 and adapter8 freezes are
separate and unchanged. No source-lease, runtime-provider or Caret main edits.

## Verification

The pure production comparison spec covers exact configuration matching and
image/argv/env/workdir/user/mount/ROFS/native-identity/generation mismatches, plus
defensive argv/nested-mount copying. These DATA-only tests do not mint native
evidence. Actual signed Host fixture checkers assert successful create/start has
the caller's exact runtime, writer and retained reservation; mismatch prevents start without releasing the reservation,
and a pending cooperative native cleanup retains its canonical continuation.
The actual admitted Host harness, disposable images and native fault execution
remain NOT_RUN/NOT_COVERED. Source checks alone do not qualify launch or cleanup.
