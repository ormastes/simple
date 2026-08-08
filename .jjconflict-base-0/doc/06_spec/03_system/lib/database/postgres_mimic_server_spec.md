# PostgreSQL mimic server

## PostgreSQL-like session on PureDatabase

1. Start a PostgreSQL-like database session.
2. Confirm authentication-ok startup semantics.
3. Create, write, and query through the pure-Simple engine.
4. Confirm row-set results.
5. Observe transaction state (`T` then `I`) and terminated-session isolation.

## Compiled database artifact for interpreter callers

1. Request interpreter execution while production fallback is disabled.
2. Confirm selection resolves to the cached SMF executable.
3. Confirm the artifact is production-ready and compiled.

This evidence does not claim PostgreSQL binary wire, TLS, SCRAM, COPY,
replication, or full SQL parity.
