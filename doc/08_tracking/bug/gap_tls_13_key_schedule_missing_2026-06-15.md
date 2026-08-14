# GAP-TLS-2: TLS 1.3 server key schedule is incomplete

Status: OPEN
Owner: Pure-Simple TLS protocol lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` advertises TLS policy, but
the current Pure-Simple server composition has no complete TLS 1.3 handshake
secret derivation, Finished verification, traffic-key transition, or record
protection path for accepted sockets.

Unblock when RFC known-answer scenarios and a live loopback handshake prove the
server key schedule and protected application-data transition without routing
protocol behavior through a foreign TLS server.
