# PostgreSQL mimic server architecture

Dependency direction:

`TCP/Unix transport -> PostgreSQL wire codec -> PostgresMimicServer -> PureDatabase`

The implemented session core owns startup identity, session lifecycle, simple
query dispatch, PostgreSQL command tags, SQLSTATE classification, and
transaction-status reporting. `PureDatabase` remains the sole SQL execution and
persistence owner. Transport and binary wire framing remain separate adapters.

Production composition selects `build/database/postgres_mimic_server.smf`, a
compiled `.lsm` library, or a native executable. Interpreter-mode tools connect
to or load the cached artifact; they do not interpret database hot paths.

Current compatibility boundary: session/simple-query semantics are implemented.
Binary PostgreSQL v3 framing, TLS, SCRAM, extended query, COPY, replication, and
live TCP acceptance require later contract-tested adapters and must not be
advertised as supported yet.
