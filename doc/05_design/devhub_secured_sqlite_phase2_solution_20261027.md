<!-- codex-design -->
# DevHub secured SQLite solution with the pinned Phase 2 producer

Date: 2026-10-27. Status: proposed implementation and acceptance plan; not an implementation or runtime PASS report.

## Scope and delivery order

Messenger database access is a required main feature. The user's instruction to land the other fixes first permits an independent first PR; it does not waive the database requirement. Start database implementation on the next branch after that PR lands. This document may travel with the first PR as planning only.

Phase A delivers secure, working production Messenger reads against a freshly provisioned encrypted database: rooms, members, history, and message fetch. Keep externally owned Messenger databases read-only. Creating an owned acceptance database does not imply adding write commands to Messenger. Phase B improves session reuse and bounded reads. A production owned-database creation API is a separate deliverable if required; it must not delay proving the read path merely to expand the product's write surface.

Use the existing producer without rebuilding it:

* Path: `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`
* SHA-256: `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`

Application/library source workarounds and narrowly tested runtime-provider fixes are allowed. Do not substitute a new compiler, sweep in a Rust seed replacement, bypass the codec registry, or replace real assertions/runners with successful stubs. Existing Messenger RTS01 and SSpec investigation limits remain in force; they are unresolved product/tooling defects, not external infrastructure.

## Research basis and confirmed source observations

Astra synthesized the following source research from Sol (`sol_db_preresearch`, callback ownership and historical evidence) and Terra (`terra_db_preresearch`, storage geometry, snapshot security, memory ownership, and efficiency). These observations are source findings, not proof of the current native panic's cause.

| Owner/path | Observation and consequence |
|---|---|
| `src/app/devhub/messenger/adapter/db_common.spl`: `_read_table`, `messenger_db_list_rooms`, `messenger_db_list_members`, `messenger_db_history`, `messenger_db_fetch_message` | Each operation opens, reads a table, and closes. Preserve policy gates, schema selection, typed errors, and read-only intent while changing storage mechanics. |
| `src/lib/nogc_sync_mut/database/server/storage_port.spl`: `storage_backend_sqlcipher4_open`, `DatabaseStoragePortV1.open` | Backend dispatch already uses `(backend.open_fn)(...)`; codec open/decode/close still use method spelling. The encrypted opener reads/decrypts a complete image. |
| `src/lib/nogc_sync_mut/database/codec/codec_registry.spl`: `PageCodecV1`, registry resolution | Factory dispatch uses `entry.factory(codec_id)`. Preserve registry admission and configured codec selection. |
| `doc/08_tracking/bug/runner_callback_field_owner_workaround_2026-10-11.md`, issue #2980 | Historical indirect function-field calls lost aggregate result ownership. Parenthesized field calls fixed parsing; a concrete typed identity-return helper repaired one historical ARM aggregate boundary. A typed local alone did not. This is a lead, not Windows P2 proof. |
| `src/lib/nogc_sync_mut/database/sqlite_format/{reader,pager,btree}.spl` | `sqlite_format_read_table_bytes` materializes rows; `SqlitePager` caches pages but retains the full snapshot. A small top-K result alone does not bound database reads or retained image memory. |
| `src/lib/nogc_sync_mut/database/sqlite_format/wimage.spl`: `sqlite_format_create_image`, `_build_table_pages`, `_build_schema_pages`, `_write_header` | Current writer assumes usable page size equals 4096 and writes reserve byte zero. It cannot safely feed SQLCipher by truncating 80 bytes after packing. Secondary-index creation is not supplied by this writer. |
| `src/lib/nogc_sync_mut/database/codec/sqlcipher4_page.spl` | Profile uses 4096-byte pages with 80 reserved bytes and authenticates ciphertext before CBC decryption. Preserve that ordering and geometry. |
| `src/lib/nogc_sync_mut/database/codec/sqlcipher4_keys.spl`, `sqlcipher4_page.spl` | Comments explicitly admit unwiped frozen KDF-result copies and environment-secret text. Wiping a mutable copy does not erase those originals. |
| `storage_port.spl`: encrypted-open error exits | Later-page authentication failure and decrypted-header rejection can leave previously accumulated plaintext unwiped. A whole-file byte copy also does not establish a consistent live SQLite/WAL snapshot. |

## Phase A: establish working reads with finite boundary evidence

Provision a fresh, private, multi-page SQLCipher-compatible database containing realistic room/member/message tables, Unicode, escaped text, equal sequence values, and overflow payloads. Prefer a real reference SQLCipher provisioner for the initial fixture so the current writer's reserve geometry does not confound read diagnosis. Keep secrets out of argv and logs. Reference provisioning is acceptance setup, not a substitute production reader.

Record the producer hash, source revision, fixture geometry, artifact hash, stage reached, and exact error. Add nonsecret stage evidence at these real boundaries in one planned diagnostic path:

1. Policy/schema/`target.db` admission.
2. Configured storage-backend dispatch and codec registry factory return.
3. Key-session return and first-page authentication/decode.
4. Later-page decode and SQLite header/schema admission.
5. Concrete row return and Messenger JSON result.

Do not rerun the exhausted unchanged RTS01 fixture. A new acceptance run must exercise substantive secure-provision/read work and produce new evidence; renaming a fixture or opening a new branch does not reset the six-cycle cap. Record carried-forward cycles and stop when the applicable limit is reached. If it prevents the next needed experiment, report the limitation rather than silently resetting it.

At a demonstrated function-field boundary, first use explicit `(receiver.callback)(...)` spelling, including the factory when relevant. If evidence still identifies aggregate-owner loss there, use a small concrete identity-return helper matching the actual result type, such as `Result<CodecSessionV1, Sqlcipher4Error>`. Keep original failures and payloads intact. Do not scatter generic wrappers, assume Option unwrapping is the cause, or call a backend directly to skip registry policy. Rebuild only the affected application acceptance artifact with the pinned producer; never rebuild P2.

Phase A is complete only when actual production entry points return the expected rooms, members, ordered history, and fetched body after the provisioner has closed the database, and negative cases below fail correctly. A passing leaf selector or page decoder alone is insufficient.

## Secure storage contract

Introduce a snapshot owner below the existing port, with a proposed interface `open_read_snapshot(path, policy) -> Result<ReadSnapshot, StoragePortError>`. Names are design proposals, not existing APIs.

* Open a regular file through a no-follow, read-only native handle and retain its identity for the session. Do not change source bytes, permissions, journals, or checkpoints.
* Support a consistent committed view using actual SQLite-compatible locking and validated WAL overlay, or return a typed `SnapshotUnavailable` for unsupported/live journal states. Checking whether `-wal` exists and then copying the main file is not a race-safe implementation. A quiescent external snapshot requires a real ownership/locking guarantee.
* Admit size, page count, reserve geometry, table/schema bounds, and cache budget before allocating proportionally. Reject malformed page references and overflow chains without unbounded traversal.
* Authenticate each page before releasing its plaintext. Use a common externally safe authentication failure for wrong keys and damaged authenticated pages; do not return partial rows after failure.
* If reads become lazy, explicitly describe their guarantee as authentication of accessed pages. Provide a separate full-integrity operation for detecting tampering in unvisited pages; do not claim that a successful limited query authenticates the entire file.

Make key, plaintext-page, and snapshot ownership explicit. Route every failure and normal close through cleanup that wipes accumulated plaintext, decoded scratch pages, session keys, and owned password buffers. Eviction must wipe pages before releasing them. Returned message text is deliberately application-visible; define its lifetime rather than pretending that returned copies were erased.

Close the frozen-copy gap at the actual provider boundary, for example by deriving into a caller-owned wipeable buffer or retaining keys in an opaque native session with explicit destruction. Test that provider independently through its real owner. Avoid manufacturing an additional frozen return value just to wipe its mutable copy. Environment-secret text cannot support a complete-erasure claim while the runtime retains immutable copies; use a bounded secret-provider interface for that claim, or explicitly retain the limitation and leave security completion open.

## Session and read-efficiency design

Add a typed `MessengerReadSession` owning the admitted snapshot, codec session, schema profile, schema metadata, and bounded page cache. Proposed operations are `open`, `list_rooms`, `list_members`, `history`, `fetch_message`, `check_integrity`, and `close`; existing one-shot API wrappers may own a short session for compatibility. Long-lived callers must actually reuse the session to obtain the benefit.

Perform one configured key-derivation setup and one schema discovery per session; do not repeat them for each operation. Derivation setup includes the profile's required key derivations, not literally a single PBKDF invocation. Invalidate the session on snapshot identity change; never reuse authenticated plaintext against a different file generation.

Replace whole-table row materialization with a bounded iterator and an authenticated random-access pager. A bounded scan is the explicit fallback where no supported index exists. Implement actual index B-tree seek only for supported schemas/indexes, including a stable cursor and correct row lookup; do not advertise indexed latency from a synthetic index that the production reader cannot traverse.

Preserve `src/app/devhub/messenger/adapter/history_rows.spl` semantics: lowest sequences ascending, source-order stability for equal keys, and validation of every matching sequence even outside the selected limit. Early indexed termination changes the last rule. Either establish validation separately or make a deliberate, documented contract change with acceptance coverage. Do not silently reinterpret history as latest-first.

Instrument key setups, schema discoveries, physical bytes/pages read, authenticated/decrypted pages, cache hits/evictions, peak owned bytes, and elapsed open/query time. Initial structural budgets are one setup/schema discovery per session and a configurable fixed page-cache bound. Record cold/warm measurements on small and large databases on the same host. For indexed queries, require measured read growth consistent with the implemented seek plus result pages; for scans, report linear reads honestly. Set numeric latency targets after this baseline, before accepting the optimization; there is no measured latency claim in this plan.

## Owned database creation, when required

If acceptance must use the repository writer, or a production creation API is required, add an explicit reserved-byte parameter through every writer sizing/packing path: schema, table leaf/interior cells, overflow pages, content offsets, and header reserve byte. For this profile use page size 4096, reserve 80, usable 4016; honor the first page's additional SQLite header offset. Preserve reserve-zero SQLite behavior for existing callers.

A proposed `create_owned_sqlcipher_database(path, schema, rows, secret_ref)` must use cryptographic randomness for file salt and page IVs, the real configured SQLCipher codec, and private native staging before secret bytes are written. Publish atomically without overwriting an existing destination, check flush/publication failures, and clean up/wipe on failure. A deterministic fixture RNG is not a production default. Do not create a plaintext temporary database on disk.

Require independent reference SQLCipher open/query/integrity checks of produced files, and production reads of reference-produced files. Include page-boundary and overflow cases that would expose a 4096-versus-4016 packing mistake. Reference tooling's absence is an explicit interoperability qualification gap, not permission to label self-roundtrip as independent verification.

## Implementation lanes and acceptance

After the first PR lands, the merge owner freezes shared interfaces and schedules native builds. Suggested lanes retain the research ownership: Sol isolates and fixes the proven callback/result boundary; Terra implements snapshot and wipe ownership; the root owner integrates production sessions and provisioning; Astra reviews security, behavior, and exact final commit. These are assignments for the next phase, not claims that work has started. No additional sidecars are required for this finite scope.

| Acceptance group | Required evidence |
|---|---|
| Working Messenger feature | Closed fresh encrypted fixture reopened through configured production registry; rooms/members/history/fetch results asserted, including Unicode, escapes, ties, missing records and malformed rows. |
| Authentication and cleanup | Missing secret, wrong key, first/later-page tamper, corrupt decrypted header, and injected read/decode failures produce no partial output; owned sensitive buffers and private staging are checked after failure/close. Full-integrity test includes unvisited-page tamper. |
| Read-only snapshot | Source bytes and metadata remain unchanged; live writer/checkpoint race yields a valid committed snapshot or explicit refusal. Symlink/nonregular input is rejected according to the snapshot contract. |
| Provisioning | Private file permissions/Windows DACL, no overwrite, CSPRNG failure refusal, correct reserved geometry, overflow data, and independent SQLCipher interoperability. Apply production-creator cases only if that API is implemented. |
| Efficiency | Same-session setup/schema counts, bounded cache/row retention, actual cold/warm timings, physical-read counters across database sizes, and supported-index versus fallback-scan evidence. |
| Honest execution | Real production calls and negative controls; captured exit status and stage evidence. SSpec's unresolved producer compatibility is reported separately. A native acceptance artifact can prove its actual operations without claiming SSpec was repaired. |

Every temporary workaround must carry `@workaround`, a registered canonical BugDB ID, affected producer hash, narrow boundary/reproducer, and a removal condition tied to the eventual producer/provider repair and passing retained regression. Use the canonical append-preserving registration workflow for legacy BugDB rows; do not regenerate the registry or invent tags with unregistered IDs. Reuse #2980 as research evidence without declaring it the current cause before isolation.

The completion report must separate implemented behavior, actual passing acceptance, unexecuted cases, remaining producer defects, and genuinely external dependencies. Neither this design nor the independent first PR constitutes a working Messenger database claim.
