# Pure Db Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/dbfs/pure_db_spec.spl` |
| Updated | 2026-05-28 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SPipe scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/dbfs/pure_db/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/dbfs/pure_db/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/dbfs/pure_db/combined.log` |
| `output.log` | Log file | `build/test-artifacts/dbfs/pure_db/output.log` |
| `run.log` | Log file | `build/test-artifacts/dbfs/pure_db/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/dbfs/pure_db/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/dbfs/pure_db/stdout.log` |

## Scenarios

- creates in-memory database
- creates table
- rejects duplicate table
- allows CREATE TABLE IF NOT EXISTS
- inserts and selects rows
- selects with WHERE clause
- selects specific columns
- deletes with WHERE clause
- updates rows
- round-trip create-insert-select-delete
- reports table_exists correctly
- rejects query on closed database
- searches text columns with BM25 ranking
- supports FTS5-compatible search alias
- search reflects updated and deleted rows
- invalidates cached FTS search index after writes
- supports alternate lightweight search algorithms
- supports DROP TABLE
- supports DISTINCT
- supports LIKE
- supports COUNT aggregate
- supports INNER JOIN
- supports ORDER BY ASC
- supports IS NULL
- supports IS NOT NULL
- supports NOT in WHERE
- supports LIMIT
- supports LIMIT OFFSET
- supports parameterized queries
- supports LENGTH function
- supports UPPER and LOWER functions
- supports TRIM function
- supports SUBSTR function
- supports REPLACE function
- supports ABS function
- supports COALESCE function
- supports IFNULL function
- supports multiple aggregates
- supports column alias AS
- supports BEGIN and COMMIT
- supports ROLLBACK
- supports ALTER TABLE ADD COLUMN
- supports nested operations in transaction
- supports arithmetic in SELECT
- supports CASE WHEN
- supports CASE WHEN without ELSE
- supports INSERT OR REPLACE
- supports multi-statement SQL
- persists to file and reloads
- full SQL feature integration
- handles empty table queries
- handles special characters in text
- supports CREATE INDEX
- supports CREATE UNIQUE INDEX
- supports DROP INDEX
- FTS uses shared engine for bm25_search
- update_by_key updates a row via typed API
- update_by_key returns 0 for non-existent key
- update_by_key updates PK column and fixes PK map
