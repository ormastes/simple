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

**Revalidated 2026-11-02: still plausible because open; an active source workaround is not a compiler/provider fix; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-03 (fixlane): regression spec added; status fix-implemented-verification-pending.** The classifier fix is in source (`result_tuple_payload.spl`: `native_result_tuple_integer_type` keeps u8/u16/u32/u64 and i8..i64 slots; arrays/slices keep element metadata). New spec `test/01_unit/compiler/mir/result_tuple_slot_metadata_spec.spl` (4 examples) passes 4/4 on the seed-interpreted compiler and fails 0/4 on the pre-fix `result_tuple_payload.spl` (`wrapper_owned_native_tuple_payload_type` absent). The older `result_try_provider_tuple_spec.spl` is stale (0/10 on current source: `module_surfaces_from_modules` now returns Result, `result_tuple_payload_type` no longer exists, consumer HIR reports 1 error) and is NOT evidence; repair or retire it separately.
Retire the explicit bindings in `src/lib/nogc_sync_mut/database/sqlite_format/cell.spl` (3 `@workaround` sites) only after a stage3 built from this source: (1) `bin/simple test test/01_unit/compiler/mir/result_tuple_slot_metadata_spec.spl`; (2) native-build `test/fixtures/devhub/native_result_unsigned_tuple/main.spl` and run it (u64 maxima and byte arrays survive `?`); (3) remove the explicit bindings and run the SQLite parser + production Messenger read/wrong-key/tamper regressions.
