# test_db struct-name collision: 8 structs declared twice with different field layouts (test_extended vs test_runner test_db_types) — blocks stage2 mcp/test_runner tool builds (2026-11-16)

**Status:** OPEN (rename or merge one family; sibling of the #9735 method dedup)
**Area:** src/lib/nogc_sync_mut/database/test_extended/types.spl vs
src/lib/nogc_sync_mut/test_runner/test_db_types.spl
**Evidence:** after the method-ambiguity dedup (#9735, verified: ambiguity
errors 0), the mcp and test_runner stage2 tool builds still fail MIR with:
- `[mir-lower] struct/class name 'X' re-registered with a DIFFERENT field
  list ...; keeping EXISTING` for ChangeEvent, CounterRecord, TestRecord,
  TimingRun, TimingSummary (and, by declaration scan, FileRecord, RunRecord,
  SuiteRecord — 8 shared names total);
- `unresolved method call: slice ... at src/lib/nogc_sync_mut/database/test_extended/database.spl:1052`;
- `unresolved method call: operator overload for struct .../database/core.spl::StringId (no matching __eq__ ...)`.

## Root cause

The two modules are two independently-evolved test databases: test_extended
is the shared analytics library (its types are imported across many modules);
test_db_types.spl is the test_runner lane's internal recording DB. They
reused the same struct names with different fields. MIR's bare-name struct
registry keeps the first registration in a compilation, so a closure pulling
both (the mcp and test_runner tool closures) resolves field accesses against
the wrong shape for one family.

## Fix direction

Rename the test_db_types family (e.g. TestDbChangeEvent / TrdChangeEvent
prefix) — test_extended's names are the broadly-imported public surface — or
merge the two databases if they are actually one concept drifted apart.
The rename must cover the struct declarations and every use inside the
test_runner lane's files, then be verified by the same mcp/test_runner
stage2 builds that currently fail.

## Note

This is the second duplication layer in the same library family; the method
layer was fixed in #9735. A one-declaration-per-name CI guard (structs and
impl methods) would prevent recurrence.
