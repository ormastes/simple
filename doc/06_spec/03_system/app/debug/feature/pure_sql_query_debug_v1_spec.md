# Pure-Simple SQL Query Debugging

> This scenario proves the first executable part of REQ-017 through the canonical embedded database engine. In this repository, “Simple SQLite” means `PureDatabase`, the SQLite-compatible engine implemented in Simple. The test therefore does not introduce or silently select the C `sqlite_sffi` wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple SQL Query Debugging

This scenario proves the first executable part of REQ-017 through the canonical embedded database engine. In this repository, “Simple SQLite” means `PureDatabase`, the SQLite-compatible engine implemented in Simple. The test therefore does not introduce or silently select the C `sqlite_sffi` wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_unified_debugging_evidence.md |
| Plan | doc/03_plan/sys_test/simple_unified_debugging_evidence.md |
| Design | doc/05_design/simple_unified_debugging_evidence.md |
| Research | doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md |
| Source | `test/03_system/app/debug/feature/pure_sql_query_debug_v1_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario proves the first executable part of REQ-017 through the
canonical embedded database engine. In this repository, “Simple SQLite” means
`PureDatabase`, the SQLite-compatible engine implemented in Simple. The test
therefore does not introduce or silently select the C `sqlite_sffi` wrapper.

The production path creates a table, inserts a private value, executes a real
parameterized SELECT, and observes it through `pure_query_debug_observe_v1`.
The result carries causality, a sanitized template, typed bind shape, a stable
statement digest, timing, row count, and the plan used by this implementation.

This slice establishes the contract and privacy behavior needed before richer
plan, wait, lock, WAL, checkpoint, savepoint, and replay evidence is added.

## Contract

The query observation includes:

- engine and dialect identity;
- logical database and schema;
- connection, transaction, and savepoint identities;
- application source anchor;
- trace, task, and actor identities;
- digest of the sanitized statement template;
- bind types and shape, never bind values;
- estimated and actual plan labels;
- elapsed monotonic time and returned row count;
- waits, locks, cache, buffer, retry, and raw-evidence fields.

Fields unavailable in this first PureDatabase slice are explicitly labeled
`unavailable` or left empty. They are not reported as measured zeros.

## Privacy

The fixture deliberately inserts `private-name`. Neither the sanitized SQL nor
the bind-shape evidence may contain that value. Numeric literals and quoted
text literals become `?`; parameter placeholders remain `?`. Bind evidence is
limited to names such as `integer`, `text`, `blob`, `bool`, and `null`.

The statement digest is calculated from the sanitized template. Consequently,
two executions that differ only in sensitive literal values share a useful
diagnostic identity without disclosing those values.

## Causality

The caller supplies application-owned context. This scenario asserts the
transaction, source anchor, and trace ID survive the database boundary. Task,
actor, connection, schema, and savepoint fields follow the same typed record.

No global trace context is guessed. Empty context remains empty rather than
being synthesized from a process ID or current thread.

## Plans and statistics

PureDatabase currently exposes the selected source table, so the truthful plan
for this SELECT is `pure-sql:table-scan:users`. The adapter reports the same
value as estimated and actual because there is no separate runtime-plan owner
yet. It must not claim an index scan, cache hit, buffer count, or lock sample.

Elapsed time uses the existing monotonic time owner. A clock failure is
represented as unavailable rather than wall-clock time. Row count comes from
the actual returned row collection.

## Syntax and examples

Create a context without sensitive data:

```text
context = pure_query_debug_context_v1("app-db", "pool-1/conn-2")
context.transaction_id = "txn-17"
context.trace_id = "trace-17"
```

Observe a parameterized SELECT:

```text
pure_query_debug_observe_v1(
  db,
  "SELECT * FROM users WHERE id = ?",
  [DbValue.Integer(1)],
  context,
)
```

Expected evidence shape:

```text
engine=simple-pure-sql
dialect=sqlite-compatible
template=SELECT * FROM users WHERE id = ?
bind_shape=integer
actual_plan=pure-sql:table-scan:users
rows=1
```

## Failure behavior

Parse, closed-database, constraint, and query failures remain typed `DbError`
results. The observer does not convert a failed query into a successful event.
A future error-evidence API may capture sanitized failure metadata, but it must
still return the original execution failure to the caller.

## Non-claims

This scenario does not prove:

- host C SQLite `sqlite3_trace_v2` or `sqlite3_stmt_scanstatus_v2`;
- EXPLAIN ANALYZE or query replay;
- WAL/checkpoint or busy-timeout evidence;
- lock cancellation, rollback, plan forcing, or schema mutation;
- PostgreSQL, MySQL, or SQL Server adapters;
- production throughput or resource-overhead targets;
- Bootstrap 4 or native self-hosted execution.

Those remain separate live-evidence gates. This scenario is intentionally
specific: a real PureDatabase query crosses the shared QueryDebugV1 boundary
with truthful privacy, causality, plan, timing, and row-count evidence.

## Test: Observe a production-shaped embedded query

Given an in-memory `PureDatabase` containing one user row, when the application
observes a parameterized SELECT through `pure_query_debug_observe_v1`, then the
result has one row, a stable digest, sanitized SQL, typed bind shape, plan,
timing, source anchor, trace identity, and transaction identity.

## Example Details

### Observe a production-shaped embedded query

```simple
Given an in-memory `PureDatabase` containing one user row, when the application
observes a parameterized SELECT through `pure_query_debug_observe_v1`, then the
result has one row, a stable digest, sanitized SQL, typed bind shape, plan,
timing, source anchor, trace identity, and transaction identity.
"""

use std.spipe.*
use std.database.pure_sql.{PureDatabase}
use std.database.pure_sql.debug_query_v1.{
    pure_query_debug_context_v1, pure_query_debug_observe_v1,
}
use std.database.sql.types.{DbValue}

describe "REQ-017 pure-Simple SQL query debugging":
    it "observes causality, sanitized SQL, plan, and execution statistics":
        step("Given a canonical PureDatabase with one application row")
        var db = PureDatabase.memory()?
        db.exec("CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)", [])?
        db.exec("INSERT INTO users (id, name) VALUES (1, 'private-name')", [])?

        step("When the application observes its parameterized query")
        var context = pure_query_debug_context_v1("app-db", "pool-1/conn-2")
        context.transaction_id = "txn-17"
        context.source_anchor = "src/app/users.spl:44"
        context.trace_id = "trace-17"
        context.task_id = "task-4"
        val observed = pure_query_debug_observe_v1(
            db, "SELECT * FROM users WHERE id = ?", [DbValue.Integer(1)], context)?

        step("Then evidence is correlated and no bind value is retained")
        expect(observed.rows.len()).to_equal(1)
        expect(observed.debug.rows).to_equal(1)
        expect(observed.debug.sanitized_template).to_equal("SELECT * FROM users WHERE id = ?")
        expect(observed.debug.bind_shape).to_equal("integer")
        expect(observed.debug.actual_plan).to_equal("pure-sql:table-scan:users")
        expect(observed.debug.statement_digest.starts_with("sha256:")).to_equal(true)
        expect(observed.debug.source_anchor).to_equal("src/app/users.spl:44")
        expect(observed.debug.trace_id).to_equal("trace-17")
        expect(observed.debug.transaction_id).to_equal("txn-17")
        expect(observed.debug.elapsed_ns >= 0).to_equal(true)
```

## Scenarios

### REQ-017 pure-Simple SQL query debugging

#### observes causality, sanitized SQL, plan, and execution statistics

- Given a canonical PureDatabase with one application row
- When the application observes its parameterized query
- Then evidence is correlated and no bind value is retained
   - Expected: observed.rows.len() equals `1`
   - Expected: observed.debug.rows equals `1`
   - Expected: observed.debug.sanitized_template equals `SELECT * FROM users WHERE id = ?`
   - Expected: observed.debug.bind_shape equals `integer`
   - Expected: observed.debug.actual_plan equals `pure-sql:table-scan:users`
   - Expected: observed.debug.statement_digest.starts_with("sha256:") is true
   - Expected: observed.debug.source_anchor equals `src/app/users.spl:44`
   - Expected: observed.debug.trace_id equals `trace-17`
   - Expected: observed.debug.transaction_id equals `txn-17`
   - Expected: observed.debug.elapsed_ns >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Given a canonical PureDatabase with one application row")
var db = PureDatabase.memory()?
db.exec("CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)", [])?
db.exec("INSERT INTO users (id, name) VALUES (1, 'private-name')", [])?

step("When the application observes its parameterized query")
var context = pure_query_debug_context_v1("app-db", "pool-1/conn-2")
context.transaction_id = "txn-17"
context.source_anchor = "src/app/users.spl:44"
context.trace_id = "trace-17"
context.task_id = "task-4"
val observed = pure_query_debug_observe_v1(
    db, "SELECT * FROM users WHERE id = ?", [DbValue.Integer(1)], context)?

step("Then evidence is correlated and no bind value is retained")
expect(observed.rows.len()).to_equal(1)
expect(observed.debug.rows).to_equal(1)
expect(observed.debug.sanitized_template).to_equal("SELECT * FROM users WHERE id = ?")
expect(observed.debug.bind_shape).to_equal("integer")
expect(observed.debug.actual_plan).to_equal("pure-sql:table-scan:users")
expect(observed.debug.statement_digest.starts_with("sha256:")).to_equal(true)
expect(observed.debug.source_anchor).to_equal("src/app/users.spl:44")
expect(observed.debug.trace_id).to_equal("trace-17")
expect(observed.debug.transaction_id).to_equal("txn-17")
expect(observed.debug.elapsed_ns >= 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_unified_debugging_evidence.md`
- **Plan:** `doc/03_plan/sys_test/simple_unified_debugging_evidence.md`
- **Design:** `doc/05_design/simple_unified_debugging_evidence.md`
- **Research:** `doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md`


</details>
