# SimpleOS Database Service

Source: `test/01_unit/os/services/database/simple_db_service_spec.spl`

Status: source contract implemented; live RV64 QEMU proof pending. Stubs: 0.

## Primary flow

1. Send `POST /db` with `CREATE settings`.
2. Reuse the same service instance for `INSERT settings theme dark`.
3. Send `SELECT settings theme` and require the response body `dark`.
4. Confirm one table and one row remain in service state.

The boot HTTP listener owns one bounded `SimpleDbService` instance. Non-DB HTTP
requests continue through the existing web response path.

## Failure behavior

- Empty, malformed, oversized, duplicate, missing-table, and missing-key
  commands return explicit errors without mutating stored state.
- Requests are capped at 1024 bytes; commands at 256 bytes.
- The service holds at most 16 tables and 128 rows.

## Verification

Unit scenarios cover the primary HTTP flow, invalid state transitions, and both
capacity ceilings. Release evidence must additionally show live guest
CREATE/INSERT/SELECT responses and the selected `codex-41` value.
