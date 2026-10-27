# Pinned Phase 2 loses integer and byte tuple metadata across Result propagation

- Canonical ID: `phase2_result_tuple_try_binding_metadata_2026_10_27`
- Status: open; an active source workaround is not a compiler/provider fix.
- Owner: DevHub completion / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: existing P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`; no compiler rebuild.
- Source: `src/lib/nogc_sync_mut/database/sqlite_format/cell.spl`.
- Regression: `test/fixtures/devhub/native_result_unsigned_tuple/main.spl`.

Explicit typed Ok and Err bindings preserve u64 and byte-array tuple payload metadata where native Result propagation did not. Related compiler Result tuple repairs are in source, but the pinned producer has not been rebuilt and the compatibility bindings remain.

## Evidence

Earlier Messenger compilation admitted all169 MIR modules after explicit SQLite tuple bindings. Supplemental unsigned varint and truncation checks passed. Production Messenger adapter RTS01 remains unresolved; this workaround is not proof that the database read works.

## Removal condition

Retire after the actual deployed producer passes try-propagated u64 maxima and byte arrays plus the full SQLite parser and production Messenger read/wrong-key/tamper regressions. Keep the underlying bug open until then.

The standard SSpec suite, all runtime-family combinations and any claim not explicitly tied to an actual artifact remain unqualified. Record the workaround commit in the canonical BugDatabase investigation log after integration; never retire it from a source-only review.
