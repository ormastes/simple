# Dual-ingress service V2 manual

STATUS: AWAITING_VERIFICATION. All cases below are NOT_RUN.

SSpec: `test/01_unit/lib/daemon_sdk/local_gateway_service_v2_spec.spl`.

| Case | Evidence required |
|---|---|
| Per-lane capacity bounds | Invalid bounds acquire no listener and retain domain |
| Endpoint/UID policy | Aliased paths and same-UID profile refused before effects |
| Blocked startup | Neither classifier nor handler executes |
| Failed-response selector | Invalid/stale selection retains complete service |
| Empty transport stop | Domain and original failure retained after transport close |

These are invalid/empty-owner cases, not invented native success fixtures.

## Actual saturation and cross-port fixture

Source: `test/fixtures/native_gateway_service_v2/main.spl`.
Shared fixture-only CLI/clock helpers are in
`test/fixtures/daemon_sdk/gateway_cli_v2.spl`; the earlier dispatch fixture uses
the same helpers without changing its test behavior.

Build only with an admitted source-matched Simple producer and actual CoreC
runtime after explicit finite build allocation. No build or run has occurred.
Use already provisioned separate service/client UIDs and protected, traversable
endpoint directories satisfying the native policy. Do not create identities,
elevate, weaken directory policy or replace the profile with same-UID peers.

For each mode `saturation` and `cross-port`, launch fresh processes and socket
paths under their respective existing identities, with external finite timeout
and CPU0-4 allocation:

```text
<qualified-fixture> server <mode> <work-socket> <control-socket> <service-uid> <client-uid> provisioned-distinct-uids
<qualified-fixture> client <mode> <work-socket> <control-socket> <service-uid> <client-uid> provisioned-distinct-uids
```

Start the client after `LISTENING`. Each side has a 15-second internal bound.
Pass requires both zero exits and PASS markers, exact source/runtime/binary
hashes and preserved logs. This manual is not execution authorization.

In saturation mode the client opens two actual ordinary connections and sends
no frame. It retains them until the server explicitly stops. The control
request must still invoke exactly one allowed control handler and deliver its
actual response. The server requires both ordinary slots still be in receive
phase and the work handler count remain zero before transport cleanup.

In cross-port mode a request that the fixture policy classifies as Work is sent
over the control socket. The client must receive exit 75 and the canonical
control-port refusal, while both application handler counts remain zero.

Both cases use a fixture counter domain, not the production Host signer,
journal or provider. Signed Host composition, failed-open/close runtime cases,
failed-publication resolution, resource/RSS/latency, effect-job reservations and
all full-system acceptance remain unqualified. Prior native receiver/fork
campaigns remain closed and are not repeated by this manual.
