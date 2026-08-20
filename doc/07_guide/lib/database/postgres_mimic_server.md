# PostgreSQL mimic server

Use `std.database.postgres_mimic.PostgresMimicServer` for PostgreSQL-like
session and simple-query behavior backed by pure-Simple `PureDatabase`.

Terminology: `postgres_mimic` is only a PostgreSQL compatibility surface — it
is NOT "the DB server". Simple's DB server tier is `std.database.server`
(`src/lib/nogc_sync_mut/database/server/`: sessions, deny-wins capabilities,
transactions, commit-before-ack durability, framed transport), and the
Embedded DB (`pure_sql` `PureDatabase` / `SdnDatabase`) is its store port.

Compatibility currently covers startup metadata, authentication-ok semantics,
simple queries, row sets, command completion, SQLSTATE errors, transaction
status, and termination. It is not yet a drop-in network PostgreSQL server.

Compiled application entrypoints should use `postgres_mimic_open`,
`postgres_mimic_startup`, `postgres_mimic_simple_query`, and
`postgres_mimic_close`. These free façades keep method resolution inside the
database owner module and avoid the current cross-module MIR limitation.

For production, use the cached database SMF/LSM or native artifact selected by
`std.database.deployment`. Interpreter-mode callers should still use that
compiled artifact. Direct source execution is a development fallback only.

Compiled entrypoint source: `src/app/postgres_mimic_server/main.spl`. Build it
to `build/database/postgres_mimic_server.smf` (or a native executable), cache
the artifact, and invoke it with `--db <path> --query <sql>`.
