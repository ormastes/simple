# SimpleOS Database Service

Source: `test/01_unit/os/services/database/simple_db_service_spec.spl`

Status: source contract implemented; live RV64 QEMU proof pending. Stubs: 0.

## Primary flow

1. Send `POST /db` with `CREATE settings`.
2. Reuse the same service instance for `INSERT settings theme dark`.
3. Send `SELECT settings theme` and require the response body `dark`.
4. Require connection-close framing with no computed `Content-Length` header.

The boot HTTP listener calls an exported wrapper around one module-owned,
literal-initialized `SimpleDbService`. That avoids copying mutable service state
through the RV64 listener loop. Non-DB requests keep the existing web path.

## Failure behavior

- Empty, malformed, oversized, duplicate, missing-table, and missing-key
  commands return explicit errors without mutating stored state.
- Requests are capped at 1024 bytes; commands at 256 bytes.
- Body slicing clamps to the request cap instead of depending on the broken RV64
  native `text.len()` result.
- The service holds at most 16 tables and 128 rows.

## Verification

Unit scenarios cover the primary HTTP flow, invalid state transitions, and both
capacity ceilings. Release evidence must additionally show live guest
CREATE/INSERT/SELECT responses and the selected `codex-41` value.
