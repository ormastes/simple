# Gateway receive, dispatch and publication turns

Status: source implementation; executable qualification NOT_RUN.

The persistent Host service must classify a complete request before selecting
work. The former combined turn invoked its callback as soon as it observed
request EOF, which prevented control-first scheduling outside the callback.
This change separates that transition without adding a socket registry,
application journal, listener, process supervisor or grant mechanism.

## Ownership and ports

`local_gateway_receive_v2(connection)` returns the updated connection and an
optional `LocalGatewayRequestV1`. It performs at most one bounded receive
chunk. A request becomes ready only after canonical framing, actual EOF,
UTF-8 decoding and a fresh native peer observation. Receiving and repeatedly
inspecting readiness neither claim dispatch nor call a handler. Ready metadata
is absent from blocked, sending and completed turns.

`local_gateway_dispatch_owned_v2(owner, connection, handler)` accepts ready
phase 5 only. It rechecks the actual peer and consumes the existing native
one-use request claim before calling the handler. The returned domain owner
is assigned before response correlation, encoding, allocation, descriptor
staging or publication. Every failure retains that owner and the connection.
Copied ready connections cannot invoke the callback again after the native
claim. Application authorization remains the callback's responsibility.

`local_gateway_publish_v2(connection)` advances one response chunk or the
write-half-close. It cannot invoke a handler or restage a descriptor. Native
partial-byte accounting and transfer ownership remain unchanged. A publication
failure does not roll back the domain transition or authorize its repetition.

`local_gateway_turn_owned_v1` delegates to these same transitions and retains
its immediate-dispatch behavior for existing consumers. The connection adds
an optional cached ready request with a default, preserving existing named
constructors. No wire schema or native ABI changes.

## Host composition and remaining work

The Host adapter owns classification after its installed peer-policy mapping,
root/scope/action and request checks. The agreed initial classes are mapped
`host-status` as control/read and allowed validate/prepare/parent-budget as
work. Classification does not authorize the operation or bypass the callback.
Effect routes remain unavailable until actual provider ticket/commit and
native deferred-launch ports exist.

A complete service still needs finite connection/job admission, reserved
ingress/control capacity, aggregate frame/response memory limits, fair bounded
polling, startup/shutdown retention and the actual Host application consumer.
These functions are scheduling seams, not an implemented persistent scheduler.
Synchronous provider probes, process-governor waits and CLI resolver calls must
not run inside health/control callbacks. Filesystem/WAL operations and native
preparation latency require separate evidence; zero-wait socket IO is not a
hard real-time service guarantee.

## Validation

Five SSpec cases cover invalid/stopped owner paths and callback prevention.
The executable two-process fixture covers real receive readiness, copied
native claim rejection, successful delivery, correlation failure with updated
domain retention and actual native-close-induced publication failure. It uses
already provisioned distinct UIDs; it creates no identities and performs no
privilege changes. Both test sets are NOT_RUN. The earlier receiver-only native
PASS does not qualify these Simple callbacks or authenticated sender paths.
