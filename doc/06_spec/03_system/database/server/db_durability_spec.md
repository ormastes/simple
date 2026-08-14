# DB durability: acknowledged commit, crash boundaries, and retry identity

Source: `test/03_system/database/server/db_durability_spec.spl`

## Primary operator flow

1. **Commit and recover one durable transaction.** Open an authenticated
   session, stage a write, commit it, and inspect the database through a fresh
   disk reader rather than the server's in-memory state.
2. **Check the P3/P4 boundary.** A crash before persistence leaves the old
   durable value; a mid-persist crash leaves the authoritative file intact; a
   crash after the rename leaves the new value. The persisted file is the
   absolute oracle.
3. **Retry one commit id without reapplying.** Reopen the database after the
   acknowledgement is treated as lost and submit the same principal-bound
   commit identifier. The stored value and applied-count receipt remain stable.
4. Reusing that identifier from another principal or for different transaction
   content is a conflict.

## Calibration and evidence boundary

The executable source includes unconditional controls and injected-violation
oracles for durability. A deliberate-red run and green restoration transcript
has not been produced in this lane because the admitted Stage-4 runner is
unhealthy. This manual therefore records authored coverage, not runtime or
generated-doc provenance.

No executable `.spl` is stored below `doc/06_spec`; this manual contains no
stub scenario.
