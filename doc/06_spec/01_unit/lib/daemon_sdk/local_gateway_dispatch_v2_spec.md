# Gateway dispatch V2 manual

STATUS: AWAITING_VERIFICATION. No new executable tests have run.

Executable SSpec: `test/01_unit/lib/daemon_sdk/local_gateway_dispatch_v2_spec.spl`.

| Case | Actual assertion | Status |
|---|---|---|
| Blocked readiness | Cached request is not exposed; connection/error retained | NOT_RUN |
| Dispatch before EOF | Handler forbidden; domain and connection retained | NOT_RUN |
| Publish before dispatch | No send; ready connection retained | NOT_RUN |
| Deadline failure | Handler forbidden; domain and prepared response retained | NOT_RUN |
| Legacy stopped turn | No callback or repeated publication | NOT_RUN |

These cases deliberately use invalid/stopped owners and never manufacture a
successful native connection. They do not substitute for the following test.

## Actual two-process fixture

Source: `test/fixtures/native_gateway_dispatch_v2/main.spl`.
Build only with an admitted source-matched Simple producer and actual CoreC
runtime, under an allocated bounded build slot. No build or run is authorized
by this manual. No such qualification has occurred.

An administrator must already have provisioned separate service/client UIDs
and an approved, protected traversable socket directory satisfying the native
listener/connect policy. Do not use `setuid`, create users, weaken the path
policy, or substitute a same-UID fixture. Start each side under its existing
identity. For each mode `success`, `correlation`, and `publication`, use a fresh
socket pathname and processes. Both commands require an external finite
timeout and the shared CPU budget:

```text
<qualified-fixture> server <mode> <socket> <service-uid> <client-uid> provisioned-distinct-uids
<qualified-fixture> client <mode> <socket> <service-uid> <client-uid> provisioned-distinct-uids
```

Start the client only after the server reports `LISTENING`. Each process has
an internal 15-second bound. Success requires both exit codes zero and both
PASS markers, plus exact source/runtime/binary and log evidence.

The server receives actual canonical bytes and EOF, observes the real peer,
then checks repeat readiness before dispatch. Its counted handler advances
17 to 18. A copied ready connection must fail native claim without invoking
the forbidden second handler. Success mode delivers the actual reply.
Correlation mode deliberately returns a different request ID and verifies
that owner 18 and its response survive the encoding/publication refusal.
Publication mode closes the actual accepted native connection after dispatch,
then requires publication failure while retaining owner 18 and its prepared
response; the stopped legacy turn must not invoke again. The client requires
complete response success only in success mode and actual failure otherwise.

All three modes are NOT_RUN and blocked on the qualified producer and
provisioned distinct-UID fixture. This is an SDK counter-domain test, not a
signed Host application-grant, descriptor handoff, scheduler or full daemon
acceptance result. Existing receiver-only evidence remains historical and is
not rerun for this change.
