# Bounded dual-ingress gateway service V2

Status: source implementation; all executable qualification NOT_RUN.

Requirement DAE-04 needs a persistent owner and responsive control scheduling.
A single listener with control-first ready requests cannot reserve admission
when ordinary peers fill all slots without completing a frame. The selected
policy therefore uses two separately configured sockets backed by the SAME
canonical Unix owner and the SAME Host peer-policy mapping. It introduces no
socket registry, application journal, supervisor or wire authorization field.

## Owner and admission

`LocalGatewayServiceV2<T>` retains exactly one domain `T`, configuration, both
listener owners and separate connection arrays/cursors. Configuration selects
one already installed client UID, a distinct actual service UID, two distinct
trusted endpoint paths, 1–16 ordinary slots, 1–4 control slots and a request
timeout of 1–30000 milliseconds. The Host supplies these trusted startup values;
requests cannot select them. Native listen independently checks service EUID,
and accept observes/matches actual peer credentials.

`local_gateway_service_open_v2(owner, config)` always returns the whole service,
including a domain and partial listener acquisition on failure. Configuration
and both bounded arrays are prepared before listener effects. The control
listener opens first. Phase 1 means both listeners are acquired; phase 4 is a
blocked open retaining everything acquired so far. Opening this transport is
not proof of Host startup reconciliation or provider readiness.

Every turn visits all reserved control slots, then one ordinary slot in round
robin order. Each slot advances one accept, receive, dispatch, publication or
cleanup step. An ordinary slot cannot use a control slot. The existing frame
limits apply independently: 2 MiB request payload, 8 MiB response payload and
bounded headers. Admission bounds the number of retained frames/responses;
these logical byte limits are not measured RSS, and encoding may retain copies.
The maximum service allocation is 20 connections plus two listeners in the
existing 64-slot native registry. A future provider job dispatcher must budget
ALL its additional native connections against that shared capacity before
claiming reserved control availability with effects enabled.

## Classification and dispatch

The Host maps its actual classifier to `LocalGatewayDispatchClassV2` only after
installed peer-policy/root/scope/action/request checks. Control ingress accepts
`ControlRead` only. Work there receives a one-use exit-75 refusal; classifier
failure receives exit 77. Neither invokes the application handler. The ordinary
lane may dispatch either authorized class through its bounded cursor. The Host
callback revalidates its policy at actual dispatch; scheduling classification
never becomes operation authorization.

The landed receive/dispatch/publish core retains native one-use claims and
assigns the returned domain owner before fallible response processing. Failed
publication with a prepared response remains in its slot, including any pending
byte descriptor. The owner may explicitly call
`local_gateway_service_discard_failed_v2(service, control_lane, slot_index,
expected_connection_token)` after accounting for the domain outcome. Exact
token comparison prevents a stale slot selector from disposing a replacement
connection. This closes transport only, never a process, journal or reservation.
Unconfirmed native close continues occupying its slot. There is no automatic
request replay or implicit removal of uncertain ownership.

## Shutdown and Host composition

`local_gateway_service_stop_v2` immediately stops admission and attempts bounded
exact listener/connection cleanup. It returns the entire service on every path.
Phase 3 means transport handles are consumed; the domain `T` still belongs to
the caller. Close errors remain visible even if handles were consumed. The SDK
does not close a Host journal or release native jobs/capacity.

The Host production wrapper owns shutdown ordering: close its canonical writer
first, replace the former live domain with a cleanup-only authenticated recovery
state on any non-success, and keep its control channel. Only exact successful
writer release permits final transport stop and success exit. No wire stop
action or UID-only stop authority is introduced here.

This recovery channel exists only for a fully opened phase-1 service. A
partial-open phase-4 service does not poll either listener; it retains all
owners for trusted local cleanup and does not claim remote recovery readiness.

## Honest limits

This is the actual generic loop component, not a complete Host executable.
The Host bootstrap/cleanup wrapper is separate. Current application routes are
metadata status/validate/prepare/parent-budget; provider effects remain refused.
Native job slots, immutable provider tickets, asynchronous begin/commit and
qualified dynamic executable profiles remain required before effects enter this
loop. The SDK does not invent job reservations or execute synchronous probes in
control callbacks. Metadata WAL/filesystem work and arbitrary handler execution
can still block; no hard latency, hostile-control-client availability, process
recovery, multi-client-UID admission or full daemon PASS is claimed.

## Acceptance source

Five SSpec cases exercise invalid admission and retained owner/cleanup paths.
The actual two-process fixture requires pre-provisioned distinct UIDs. It fills
both ordinary slots with real incomplete connections while a control request
receives its response, and independently rejects a mapped Work request on the
control socket without invoking the work handler. All cases are NOT_RUN. The
older receiver-only C evidence does not qualify this Simple service loop.
