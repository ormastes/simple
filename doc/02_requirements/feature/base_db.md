# LibreOffice Base Requirements

## Scope

Base is the office-suite database substrate exposed through
`app.office.base_db` and the IDE Office catalog. This slice keeps the data model
text-first and in-memory, while hardening the table operations needed before
richer forms, queries, import/export, and persistent database integration.

## Requirements

- BASE-001: Base tables preserve a stable table name, ordered column schema, and
  ordered text rows.
- BASE-002: Existing append, exact-match select, and column projection behavior
  remains source-compatible.
- BASE-003: Checked row insertion rejects rows whose width does not match the
  schema and returns the original table unchanged.
- BASE-004: Exact-match filtered counting returns deterministic match counts and
  returns zero for missing columns.
- BASE-005: Exact-match updates replace one target column for all matching rows
  through a pure result object.
- BASE-006: Exact-match deletes remove all matching rows through a pure result
  object while preserving the order of remaining rows.
- BASE-007: Failed checked edits report deterministic reasons and keep the input
  table unchanged.

## Out of Scope

Persistent storage, SQL parsing, joins, typed numeric columns, form designers,
and CSV import/export remain follow-up slices.
