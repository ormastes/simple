# Secure bounded pgwire server

**Status:** PARTIAL/RED — executable socket-neutral scenarios now cover bounded
single-owner startup/query/terminate ordering, overload rejection, and graceful
completion of accepted work after drain closes admission. Live TCP/TLS,
independent PostgreSQL-client interoperability,
durability/restart, and resource-counter oracles remain unresolved and retain
fail-fast placeholders.

The unresolved live scenario is required to send incremental and concatenated
PostgreSQL v3 startup, SSLRequest, authentication, simple-query, cancellation,
and terminate frames through a bounded listener. It must verify fail-closed
sequencing, session ordering, capability enforcement, durability-before-ACK,
restart persistence, and overload counters. The current executable evidence is
limited to the socket-neutral database-owner ordering and overload/drain cases
listed above. Unsupported protocol features must produce explicit errors rather
than false compatibility.

**Executable SPipe:** `test/03_system/database/server/secure_pgwire_server_spec.spl`
