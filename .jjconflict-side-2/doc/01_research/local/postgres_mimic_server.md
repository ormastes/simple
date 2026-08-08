# PostgreSQL mimic server — local research

The active tree contains `PureDatabase`, a pure-Simple SQL/MVCC engine, and a
typed database server capsule, but no PostgreSQL wire/session compatibility
owner. `doc/05_design/lib/database/simple_db_design.md` already describes a
PostgreSQL-like storage direction. The new `std.database.postgres_mimic` layer
therefore composes `PureDatabase` and owns only PostgreSQL-facing session/query
semantics.

Production database hot paths should not execute as interpreted source. The
repository already supports cached `.smf`, `.lsm`, and native artifacts; the
database deployment policy makes compiled artifacts the default even when an
interpreter-mode caller initiates the request.
