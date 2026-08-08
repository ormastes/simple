# Web DB Hardening — Task State

## Status: CLOSED — 2026-05-20

## Scope
SQL injection prevention, parameterized query enforcement, and connection pool
safety for `src/lib/nogc_sync_mut/database/sql/`.

## Files Modified
- `database/sql/escape.spl` — validate_ident, is_dangerous_sql, is_safe_identifier
- `database/sql/pool.spl` — double-release guard, leaked_connections counter, force_release_all
- `database/sql/query_builder.spl` — SqlExpr.Raw safety guard, safe_raw constructor
- `database/sql/__init__.spl` — export new symbols

## Files Created
- `.spipe/web-db-hardening/state.md` (this file)
- `src/lib/nogc_sync_mut/database/sql/hardening_spec.spl` — spipe tests

## Decisions
- Existing query builder and prepared statement already enforce parameterization
  (all values go through `?` placeholders, never interpolated).
- Hardening adds: identifier validation, dangerous-SQL detection for Raw expressions,
  pool double-release guard, and a force-release safety valve.
- No inheritance used; all additions are standalone functions or class method additions.

## Phase
- [x] Research existing code
- [x] Implement escape hardening
- [x] Implement pool guards
- [x] Implement query builder Raw guard
- [x] Write spec tests
- [x] Commit
