# Daemon SDK owned poll turn V1

Base: merged PR7533 at5854838c6124cfa9deb6c0d985814dd9db8bfe0e.
Root and host owner agreed these interfaces before implementation:

- `DaemonOwnedResponseV1<T>` contains `owner: T` and `response: DaemonResponse`.
- `DaemonRunner.me run_poll_cycle_owned_v1<T>(owner: T,
  handler: fn(T, DaemonRequest) -> DaemonOwnedResponseV1<T>) -> T`.

## Accepted requirements

DOWNER-01: a caller supplies its domain owner and writes back the returned owner.
For each serial request, the handler result's owner becomes the current owner
immediately after the callback, before response identity checks, publication or
acknowledgement. The next callback receives that updated value. No mutable owner
is captured in a closure, stored globally, or discarded on publication failure.

DOWNER-02: the `me` receiver retains runner status/count/lock state. The domain
owner is returned on every normal exit, including idle, already stopped,
publication-blocked and acknowledgement-blocked turns. Idle/stopped turns return
the original owner. A blocked runner never calls another handler on a later turn.

DOWNER-03: one generic core retains existing serial `max_concurrent` behavior,
success-prefix acknowledgement, item/cycle/error counters and fail-stop states.
`run_poll_cycle` delegates with immutable integer state and an adapter capturing
only its immutable handler. Existing `run_loop` delegates through that legacy API.
No second dispatch implementation or new executor is introduced.

DOWNER-04: the async runner facade exports the same response struct; it continues
to delegate to the sync implementation. Host/domain-specific owners stay outside
the SDK. Callers must retain both the `me` receiver's state and returned domain
owner. No process recovery, remote effect acknowledgement, authentication or
exactly-once claim follows from this API.

## Verification surfaces

`test/fixtures/daemon_sdk/owned_poll_v1.spl` defines the real-file test oracles and
agreed helpers: `owned_poll_root`, `owned_poll_owner`, `owned_poll_handler`,
`owned_poll_rejecting_handler`, `owned_poll_cleanup`. The rejecting callback
asserts false if invoked; it never supplies an assumed successful effect.

Eight SSpec cases cover idle/stopped identity, two-handler accumulation in one
batch, response publication refusal, response identity refusal, acknowledgement
failure, one-request batch limit across turns, and failed-second-response prefix
handling. The eighth reuses the existing legacy publication-failure oracle to
verify immutable handler capture and fail-stop through the new adapter. All
cases call the actual SDK and inspect runner state/files; owner cases retain the
returned owner. Assertions do not assume directory order.
The fixture's generic owner is a concrete domain struct with root/handled/total.

`test/fixtures/native_daemon_owned_poll_v1/main.spl` selects idle/stopped, owned
publication-failure and existing legacy publication-failure cases from these
same oracles. This is the smallest initial
native diagnostic proving generic owner handling and receiver mutation without
successful request acknowledgement. Even this subset still depends on ordinary
spool admission for its publication-failure case; no hash workaround is added.
The known compiler text-hash ABI issue remains an independent dependency.

The first native diagnostic build at `094cafa9524` failed before linking because
importing `std.spec.fail` expanded the closure into `crypto.secure_memory`, where
the unadmitted producer could not resolve `fill_span` at four call sites. The
100 failed-module labels are one aggregate failure, not independent defects.
The forbidden callback now uses the equivalent built-in `assert(false)` so the
native oracle has no SSpec dependency; the actual SSpec wrapper remains intact.
This changes no product behavior and weakens no expected result. The bounded
second build at `13709568c52` reduced the closure from 100 to 71 modules but
still failed at the same four `fill_span` calls before linking. The production
entropy facade also reaches `secure_memory` through `crypto_sffi` and SHA-256;
the removed test import was not its sole dependency path. Neither attempt
produced an executable or established a generic-owner runtime verdict. See
[the diagnostic report](../08_tracking/bug/native_owned_poll_secure_memory_fill_span_2026_11_07.md).

Admitted SSpec, native execution, generated
manual scores, branch coverage, legacy callback execution and full-library/
MCP gates are not inferred from source review. A generic `me`/adapter compilation
failure must be attributed to the actual toolchain, not hidden with another
framework. Build slots and exact-source review belong to the Astra lead/root.
