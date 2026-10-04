# Bootstrap driver leaf owner resolution

The early Phase4 full CLI/interpreter HIR failures reported `std.io` missing
`file_exists` in `driver_source_pipeline_parsing.spl` and unresolved
`rt_hash_text` in `shb_extractor.spl`.

Against frozen integration f6026d340a59de8a35389eba53f540d1d5c155a9,
the parse-shard claim imports now use the existing `std.io_runtime` file
facade. The SHB extractor calls its already imported `shb_source_hash`, which
delegates to the same `std.io_runtime.hash_text` runtime ABI. This preserves
the hash algorithm and removes the function-local foreign declaration that
the native HIR path could not resolve. It does not change shard locking or
cache publication policy.

The native fixture `test/fixtures/compiler/native_shb_symbol_hash_owner.spl`
calls actual production extraction, verifies both boundary hashes, changes
one symbol without invalidating its peer, and checks comment exclusion.
Native execution is pending coordinated full-source compilation. A clean
source diff is not evidence that either affected product now builds.

The other six assigned driver modules already have source repairs in this
integration: persisted_graph/native_noop_admission/driver_hir_cache lock
owners, driver_hir_recovery lock and directory-list owners,
driver_source_pipeline_loading bytes conversion, and smf_serialization AST
owners. Their product/native qualification remains pending.
