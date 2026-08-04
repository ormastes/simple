<!-- codex-architecture -->
# Aspect Facets + SFM Packs — TLDR

Aspect facets preserve base layout while SFM packs provide catalogued dynamic
deployment. The implemented runtime is state-serialized and lease-based, but
production admission still awaits threaded and executable evidence.

## Core Shape

- Build-time AOP remains authoritative: prepared slots are deterministic and
  runtime dispatch never re-matches pointcuts.
- `AspectExecutionContext` solely owns the canonical loader, cache,
  coordinator, registries, projection, and lifecycle state.
- One lifecycle mutex serializes canonical transitions. Prepared advice commits
  exact generation leases, releases the mutex for native callbacks, then
  finalizes against and installs current state. Panic is fail-stop after cleanup.
- Lazy activation gates preflight and commit while exact-route pack I/O remains
  outside the lifecycle mutex. Same-route re-entry is prohibited; different
  lazy routes are globally serialized by one application single-flight.
- Facet acquire/release and unload are gated. Unload removes visibility before
  drain, validates all cache pins before physical unload, and installs partial
  transition state before propagating status or error.
- Context-free `aspect_*_transition.spl` leaves hold state algorithms without
  importing `AspectExecutionContext` or owning mutexes. The 786-line
  `aspect_application_runtime.spl` remains the ownership facade.
- Compatibility loader parameters never replace the canonical loader. No
  process-global context, second lease authority, or backend trampoline exists.

## Operational Notes

- startup: mission mode requires every startup aspect active before sealing the
  application operational.
- hot path: loader owner/address and exact generation are validated before
  zero-argument before/after callbacks; dynamic `around` remains denied.
- invalidation: variants resolve at build time; unload invalidates facet,
  advice, and projection visibility before quiesce and respects module pins.
- evidence: transition order, canonical loader use, mutex boundaries, exact
  reservations, and owner size are statically verified. `REQ-AF-008` is not
  admitted without threaded dispatch/unload and target runtime evidence;
  portable unwind/cancellation cleanup remains open.

## Open Next

- [Full architecture](aspect_facet_dynload_smf_pack.md)
- [Application runtime](../../../../src/app/startup/aspect_application_runtime.spl)
- [Prepared transition](../../../../src/app/startup/aspect_prepared_advice_transition.spl)
- [Lifecycle source guard](../../../../scripts/audit/aspect-lifecycle-gate-source-guard.shs)
