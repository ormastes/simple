# UI access SQLite demand provider integration

The executable specs are
`test/02_integration/app/ui_access_sqlite_provider_spec.spl`,
`ui_access_sqlite_demand_rejection_spec.spl`, and
`ui_access_sqlite_demand_concurrent_spec.spl` in the same directory.

1. Before the first UI store open, the demand bridge reports state 0. Opening
   the store activates the configured, digest-checked provider and reports
   state 2. Two events survive cached insert/read reuse, and an uncached
   statement is finalized after success or binding failure.
2. With a missing artifact, wrong digest, incompatible ABI, or incomplete
   symbol table, database open fails and the bridge reports state -1. Each
   case starts a fresh process because a rejection is permanent for that
   process.
3. Four pthread callers concurrently open and close in-memory connections;
   every call succeeds and the bridge reports one active provider verdict.

Native Linux aarch64 evidence on 2026-09-28: store 2/2, rejection 1/1 in
each of four runs, concurrent 1/1. The provider is absent from executable
`DT_NEEDED`. See
`doc/09_report/compiler/target5_sqlite_demand_provider_probe_2026-09-28.md`
for build scope, sizes, and limits.
