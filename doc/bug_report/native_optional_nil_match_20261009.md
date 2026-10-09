# Native Optional nil match rejects valid absent arm

Observed with the immutable Linux Stage2 producer SHA256 `2f34befeaca05b0cd4e389f4cda2e0d1558e15a8342f9b60f7fbacfa528830ae` from frozen release source `3d7141f91`.

A cross-module inline class method returning `ProbeTable?`, matched with `case Some(found)` and `case nil`, reports `enum match: unsupported arm pattern`. Replacing nil with None removes this diagnostic, while an independent payload-owner recovery defect still causes unresolved valid_rows and for-in I64 diagnostics. The reproduction is retained in the isolated diagnostic output `build/runner-owner-probe/build-option.log`; the Some/None fixture under `test/fixtures/compiler/native_cross_module_optional_class_payload` isolates the payload defect.

Production trigger: `src/lib/nogc_sync_mut/database/test_extended/database_queries.spl` matches `SdnDatabase.get_table` with Some(table)/nil. This database module is genuinely reachable through test_runner_helpers.update_test_database, RunnerTestDb.load, and load_with_migration. Excluding it would remove real persistence behavior.

The HIR literal nil survives as Literal(NilLit), whereas lower_enum_match handles enum, wildcard and binding arms. A repair must authorize nil only from a proven Optional scrutinee, use the canonical None discriminant, retain boxed/flat Option normalization and reject nil on unrelated enums. Treating nil as an unconditional wildcard is unsafe. No repair or PASS qualification is claimed by this report.
