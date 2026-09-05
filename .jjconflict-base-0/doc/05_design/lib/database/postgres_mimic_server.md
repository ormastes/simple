# PostgreSQL mimic server detail design

`PostgresMimicServer` holds a `PureDatabase`, session registry, and monotonic
session IDs. A session transitions through ready, in-transaction,
failed-transaction, and closed states. Queries classify `SELECT`/`WITH`/`VALUES`
as row-producing; other statements use `exec_sql`. Errors return SQLSTATE and a
truthful transaction byte (`I`, `T`, or `E`).

`DatabaseArtifactPlan` separates runtime deployment from database semantics.
The default is a cached SMF executable; `.lsm` and native executable modes are
available. Interpreter source is opt-in and never production-ready.
