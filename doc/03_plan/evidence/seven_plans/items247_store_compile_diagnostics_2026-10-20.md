# Budgeted-store native compile diagnostics

Outcome: FAIL. HIR completed; MIR failed in 9 of 197 modules. No executable or runtime PASS.

Command, input digests and process receipts are retained under `build/native_probe/items247-store-accounting/`.

```text
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/app/scv/db/local_store.spl::DbStoreView (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/test/fixtures/scv/store_accounting_native_probe.spl:26:8
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/app/scv/db/local_store.spl::DbStoreView (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/test/fixtures/scv/store_accounting_native_probe.spl:30:8
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_pages.spl::DbPageQuota (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/app/scv/db/checkpoint_reader.spl:118:54
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_pages.spl::DbPageEntry (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/app/scv/db/checkpoint_reader.spl:118:89
[ERROR] MIR error: MIR lowering error: B5b: match has multiple wildcard arms (arm 1 in fn lib.scv.db_pages.db_page_decode, module lib.scv.db_pages)
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct DbPageRecord (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_pages.spl:292:16
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct DbPageRecord (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_pages.spl:294:16
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct DbPageRecord (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_pages.spl:296:16
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_policy_codec.spl::DbPolicyConfig (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_checkpoint.spl:82:16
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/distributed_identity.spl::EntityRef (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_checkpoint_history.spl:87:20
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct EntityRef (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_checkpoint_history.spl:168:20
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct DbPageRecord (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_checkpoint_history.spl:152:8
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_pages.spl::DbPageEntry (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/app/scv/db/page_store.spl:333:27
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_page_records.spl::DbPageContext (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_paged_model.spl:80:8
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct <snapshot>/src/lib/scv/db_pages.spl::DbPageQuota (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_paged_model.spl:80:125
[ERROR] MIR error: MIR lowering error: unresolved method call: operator overload for struct DbPageRecord (no matching __add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__ impl) at <snapshot>/src/lib/scv/db_page_records.spl:140:8
[ERROR] MIR error: MIR lowering error: unresolved method call: bytes at <snapshot>/src/lib/nogc_sync_mut/compression/gzip/header.spl:55:18
[ERROR] MIR error: MIR lowering error: for-in over non-array iterables is not supported by native codegen yet (#143); iterate an array or use while (collection mir type: I64; module: lib.nogc_sync_mut.compression.gzip.header) at <snapshot>/src/lib/nogc_sync_mut/compression/gzip/header.spl:55:18
```

The compiler diagnostics reference more than one frozen SCV snapshot root. The input receipt records current source hashes; a refreshed producer/cache-provenance investigation is required before assuming diagnostic source-location roots attest a single current-source compile.

Resource TODO: the corrected197-module probe reached peak RSS5026400KiB
(about4.8GiB), exceeding the watchdog's documented ordinary compile acceptance
target of1,000,000,000bytes. The8GiB diagnostic cap is containment only, not
resource acceptance. Investigate the broad app-IO closure and compiler retained
state before claiming ordinary compile or Operating-B memory readiness.
