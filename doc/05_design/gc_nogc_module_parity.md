# GC/NoGC Module Parity

Design document tracking which modules exist in both `gc_async_mut/` and `nogc_sync_mut/`, what shared types live in `common/`, and the import mapping between modes.

**Updated:** 2026-05-13

---

## Dependency Direction Boundary

**Updated:** 2026-05-13

The production layering rule is:

1. Portable Simple libraries own reusable backend interfaces and records.
2. SimpleOS imports those library interfaces when it needs storage, replay, crypto, UI, or driver-facing contracts.
3. Portable `src/lib` code must not import `os.*` for common data contracts. OS-specific GPU, framebuffer, compositor, and browser adapters must be isolated as backend adapters before they can remain in `src/lib`.

Current enforced moves:

| Contract | Library owner | OS compatibility surface |
|----------|---------------|--------------------------|
| Replay `EventKind` / `ReplayEntry` | `std.nogc_sync_mut.replay.event_kinds` | `os.kernel.replay.event_kinds` re-exports |
| Replay core family facades | `std.nogc_async_mut.replay.{event_kinds,codec,types}`, `std.gc_async_mut.replay.{event_kinds,codec,types}` | `test/unit/lib/*/replay/replay_facade_spec.spl` validates package-level record, codec, and target-type exports |
| Replay top-level hosted facades | `std.nogc_async_mut.replay.{backend,event_log,trace_format,integration}`, `std.gc_async_mut.replay.{backend,event_log,trace_format,integration}` | `test/unit/lib/*/replay/replay_remaining_facade_spec.spl` validates backend-adjacent records, event log, trace package/index, and integrated session imports; canonical event-log and integration specs cover behavior |
| Replay QEMU async facades | `std.nogc_async_mut.replay.qemu_replay`, `std.gc_async_mut.replay.qemu_replay` | `test/system/replay_qemu_arch_spec.spl` and `test/unit/lib/gc_async_mut/replay/replay_qemu_facade_spec.spl` validate QEMU architecture helper exports; this file is async-backed and intentionally extra relative to `nogc_sync_mut` |
| Replay core engine family facades | `std.nogc_async_mut.replay.core.*`, `std.gc_async_mut.replay.core.*` | `test/unit/lib/*/replay/core/replay_core_facade_spec.spl` validates event records, hook contracts, no-op hook, replay engine, and global engine helpers; canonical core spec covers behavior |
| Replay VM family facades | `std.nogc_async_mut.replay.vm.*`, `std.gc_async_mut.replay.vm.*` | `test/unit/lib/*/replay/vm/replay_vm_facade_spec.spl` validates VM config, virtual timer/serial devices, and replay driver imports; canonical VM device specs cover timer, serial, and block behavior |
| Replay adapter family facades | `std.nogc_async_mut.replay.adapters.*`, `std.gc_async_mut.replay.adapters.*` | `test/unit/lib/*/replay/adapters/replay_adapters_facade_spec.spl` validates interpreter, JIT, remote, test-runner, execution, and QEMU adapter imports; canonical adapter files are syntax-checked |
| Replay process family facades | `std.nogc_async_mut.replay.process.*`, `std.gc_async_mut.replay.process.*` | `test/unit/lib/*/replay/process/replay_process_facade_spec.spl` validates process events, recorder/replayer, checkpoints, trace metadata, thread recorder, and chaos scheduler imports; canonical process event/E2E specs cover behavior |
| Replay semantic family facades | `std.nogc_async_mut.replay.semantic.*`, `std.gc_async_mut.replay.semantic.*` | `test/unit/lib/*/replay/semantic/replay_semantic_facade_spec.spl` validates semantic events, trace writer/reader exports, object registry, scenario correlation, and async timeline imports; canonical semantic event spec covers event kind behavior |
| Replay container family facades | `std.nogc_async_mut.replay.container.*`, `std.gc_async_mut.replay.container.*` | `test/unit/lib/*/replay/container/replay_container_facade_spec.spl` validates container checkpoint format and container replay driver imports |
| Resource tracker parity | `std.nogc_async_mut.resource_tracker`, `std.gc_async_mut.resource_tracker` | `bin/simple check src/lib/nogc_async_mut/resource_tracker.spl src/lib/gc_async_mut/resource_tracker.spl` validates resource metric aggregation/database helper parsing through each runtime family; canonical test-runner resource specs own behavior |
| Redis package parity | `std.nogc_async_mut.redis.*`, `std.gc_async_mut.redis.*` | `bin/simple check src/lib/nogc_async_mut/redis/*.spl src/lib/gc_async_mut/redis/*.spl` validates Redis client and pool package parsing through each runtime family; socket-backed behavior remains canonical to the no-GC sync implementation |
| Runtime value/wrapper parity | `std.nogc_async_mut.{runtime_value,runtime_wrappers}`, `std.gc_async_mut.{runtime_value,runtime_wrappers}` | `bin/simple check src/lib/nogc_async_mut/runtime_wrappers.spl src/lib/gc_async_mut/runtime_wrappers.spl src/lib/nogc_async_mut/runtime_value.spl src/lib/gc_async_mut/runtime_value.spl` validates tagged-value and runtime helper wrapper parsing through each runtime family |
| Runtime package parity | `std.nogc_async_mut.runtime.*`, `std.gc_async_mut.runtime.*` | `bin/simple check src/lib/nogc_async_mut/runtime/*.spl src/lib/gc_async_mut/runtime/*.spl` validates the pure dynamic runtime-value package parses through each runtime family |
| MCP SDK server family facades | `std.nogc_async_mut.mcp_sdk.server.*`, `std.gc_async_mut.mcp_sdk.server.*` | `test/unit/lib/*/mcp_sdk/server/mcp_sdk_server_facade_spec.spl` validates server builder counts, pagination, method detection, router sentinels, and protocol state helpers; exact subtree parity is maintained against `nogc_sync_mut/mcp_sdk/server` |
| Byte-buffer `BlockDevice` | `std.fs_driver.block_device` | `os.services.block_device` re-exports |
| Block-device family facades | `std.nogc_async_mut.fs_driver.block_device`, `std.gc_async_mut.fs_driver.block_device` | thin `export use` wrappers backed by `std.nogc_sync_mut.fs_driver.block_device` |
| fs_driver core family facades | `std.nogc_async_mut.fs_driver.{types,error,capability}`, `std.gc_async_mut.fs_driver.{types,error,capability}` | package facade specs validate path/options/capability/error re-exports |
| COSE Ed25519 | `std.math.curve.ed25519` | OS crypto remains a consumer/wrapper |
| JWT hosted RSA/ECDSA | `std.nogc_sync_mut.io.signature_ffi` | OS crypto remains a higher-level compatibility wrapper |
| Engine2D framebuffer surface | `std.gpu.engine2d.framebuffer_surface` | `os.drivers.framebuffer.fb_driver` implements the surface |
| Engine2D VirtIO-GPU surface | `std.gpu.engine2d.virtio_gpu_surface` | `os.drivers.virtio.virtio_gpu` implements the surface |
| NVFS POSIX fd table | `std.fs.nvfs_posix.fd_table` | examples may keep compatibility imports |
| NVFS POSIX remount namespace | `std.fs_driver.nvfs_posix_driver` persistent wrapper namespace | `test/integration/storage/nvfs/nvfs_name_persistence_spec.spl` no longer imports NVFS examples |
| NVFS POSIX raw/NVMe mirror | `std.fs_driver.nvfs_posix_driver` + `std.fs_driver.nvfs_arena` | `test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl` no longer imports NVFS examples |
| NVFS POSIX shim family facades | `std.nogc_async_mut.fs.nvfs_posix.*`, `std.gc_async_mut.fs.nvfs_posix.*` | `test/unit/lib/*/fs/nvfs_posix/nvfs_posix_facade_spec.spl` validates fd-id, COW shadow, fd-table refcounting, and POSIX shim driver records through each runtime family; no direct POSIX module imports are introduced |
| Browser paint/display-list types | `common.render_scene.paint_types` | `examples.browser.entity.dom.paint_types` re-exports |
| Browser transform matrix | `common.render_scene.matrix4` | `examples.browser.shared.matrix4` re-exports |
| Browser CSS value/rule types | `common.render_scene.css_types` | `examples.browser.entity.dom.css_types` re-exports |
| Browser logging/error records | `common.web.logging`, `common.web.error` | `examples.browser.shared.*` re-export |
| Browser DOM node records | `common.web.node_types` | `examples.browser.entity.dom.node_types` re-exports |
| Browser DOM attribute records | `common.web.attribute_types` | `examples.browser.entity.dom.attribute_types` re-exports |
| Browser DOM event records | `common.web.event_types` | `examples.browser.entity.dom.event_types` re-exports |
| Browser layout box records | `common.render_scene.box_types` | `examples.browser.entity.dom.box_types` re-exports |
| Browser WebGPU API types | `std.gc_async_mut.gpu.browser_engine.webgpu_types` | `test/integration/browser/webgpu_context_spec.spl` no longer imports browser examples |
| Browser QEMU guest fixture | `std.gc_async_mut.web.browser_guest_session` | `test/system/browser_in_qemu_spec.spl` no longer imports SimpleOS examples |
| DBFS in-memory arena | `std.db.dbfs_engine.arena` | DBFS conformance and throughput tests no longer import NVFS example arena |
| DBFS arena family facades | `std.nogc_async_mut.db.dbfs_engine.arena`, `std.gc_async_mut.db.dbfs_engine.arena` | `test/unit/lib/*/db/dbfs_engine/arena_parity_spec.spl` validates facade exports and behavior |
| DBFS engine family facades | `std.nogc_async_mut.db.dbfs_engine.{txn,inline_data,wal}`, `std.gc_async_mut.db.dbfs_engine.{txn,inline_data,wal}` | `test/unit/lib/*/db/dbfs_engine/dbfs_engine_facade_spec.spl` validates transaction ordering, inline data, and WAL constants through package imports |
| DBFS schema metadata family facades | `std.nogc_async_mut.db.dbfs_engine.{schema,file_meta}`, `std.gc_async_mut.db.dbfs_engine.{schema,file_meta}` | `test/unit/lib/*/db/dbfs_engine/dbfs_schema_facade_spec.spl` validates table, path resolution, directory stat, and permission helpers through package imports |
| DBFS pager/checkpoint/index family facades | `std.nogc_async_mut.db.dbfs_engine.{pager,checkpoint_ring,checkpoint,attr_index}`, `std.gc_async_mut.db.dbfs_engine.{pager,checkpoint_ring,checkpoint,attr_index}` | `test/unit/lib/*/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` validates pager writeback, checkpoint publication, ring slots, and attribute queries through package imports |
| DBFS namespace/intent/recovery family facades | `std.nogc_async_mut.db.dbfs_engine.{ns_btree,intent_log,recovery}`, `std.gc_async_mut.db.dbfs_engine.{ns_btree,intent_log,recovery}` | `test/unit/lib/*/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl` validates namespace lookups through `NsDentryKey`/`NsIno` aliases, intent-log committed scans, and recovery callbacks through package imports |
| DBFS backend family facades | `std.nogc_async_mut.db.dbfs_engine.{fs_driver,raw_nvme_arena,superblock}`, `std.gc_async_mut.db.dbfs_engine.{fs_driver,raw_nvme_arena,superblock}` | `test/unit/lib/*/db/dbfs_engine/dbfs_backend_facade_spec.spl` validates `DbfsFsDriver` behavior plus raw-NVMe arena and superblock metadata contracts; `DbfsFsDriver` remains submodule-only to avoid colliding with package-level schema keys |
| DBFS hosted metadata family facades | `std.nogc_async_mut.db.dbfs_engine.meta_store`, `std.gc_async_mut.db.dbfs_engine.meta_store` | `test/unit/lib/*/db/dbfs_engine/dbfs_meta_store_facade_spec.spl` validates explicit hosted metadata journal imports; kept out of package aggregate because it uses host file externs |
| DBFS driver family facades | `std.nogc_async_mut.db.dbfs_driver.dbfs_driver`, `std.gc_async_mut.db.dbfs_driver.dbfs_driver` | `test/unit/lib/*/db/dbfs_driver/dbfs_driver_facade_spec.spl` validates hosted construction through each family |
| DBFS driver package facades | `std.nogc_async_mut.db.dbfs_driver`, `std.gc_async_mut.db.dbfs_driver` | `test/unit/lib/*/db/dbfs_driver/dbfs_driver_init_facade_spec.spl` validates package-level re-export |
| DB acceleration family facades | `std.nogc_async_mut.db.accel`, `std.gc_async_mut.db.accel` | `test/unit/lib/*/db/db_accel_facade_spec.spl` validates canonical bitmap, scan, and text predicate exports through each family |
| DB package family facades | `std.nogc_async_mut.db`, `std.gc_async_mut.db` | `test/unit/lib/*/db/db_init_facade_spec.spl` validates package-level acceleration and DBFS driver exports |
| SQL database family facades | `std.nogc_async_mut.database.sql.*`, `std.gc_async_mut.database.sql.*` | `test/unit/lib/*/database/sql/sql_facade_spec.spl` validates helper, query-builder, schema, and value-type imports through each family |
| SQL database package facades | `std.nogc_async_mut.database.sql`, `std.gc_async_mut.database.sql` | `test/unit/lib/*/database/sql/sql_init_facade_spec.spl` validates package-level canonical SQL exports |
| Extended test database family facades | `std.nogc_async_mut.database.test_extended`, `std.gc_async_mut.database.test_extended` | `test/unit/lib/*/database/test_extended/test_extended_facade_spec.spl` validates record and host-stub imports; canonical behavior spec remains a skipped placeholder |
| Database vector family facades | `std.nogc_async_mut.database.vector.*`, `std.gc_async_mut.database.vector.*` | `test/unit/lib/*/database/vector/database_vector_facade_spec.spl` validates vector types/errors, distance helpers, vector/metadata codec round trips, brute-force index construction, and store class imports; exact subtree parity is maintained against `nogc_sync_mut/database/vector` |
| Compression family facades | `std.nogc_async_mut.compression.*`, `std.gc_async_mut.compression.*` | `test/unit/lib/*/compression/compression_facade_spec.spl` validates RLE, LZ77, gzip, and Brotli imports through each family; canonical Brotli 64 KiB boundary verification is tracked in `doc/08_tracking/bug/brotli_large_boundary_timeout_2026-05-13.md` |
| Compress package parity | `std.nogc_async_mut.compress.*`, `std.gc_async_mut.compress.*` | `bin/simple check src/lib/nogc_async_mut/compress/*.spl src/lib/gc_async_mut/compress/*.spl` validates compression package root and UPX/self-extract helpers parse through each runtime family; `io_runtime` imports are rewritten to each owning family |
| HTTP/3 family facades | `std.nogc_async_mut.http.h3.*`, `std.gc_async_mut.http.h3.*` | `test/unit/lib/*/http/h3/http_h3_facade_spec.spl` validates HTTP/3 varint/frame helpers and QPACK static table lookup through each runtime family; SETTINGS encode/decode helpers are syntax/import covered |
| MCP SDK core family facades | `std.nogc_async_mut.mcp_sdk.core.*`, `std.gc_async_mut.mcp_sdk.core.*` | `test/unit/lib/*/mcp_sdk/core/core_facade_spec.spl` validates JSON, JSON-RPC, error, and validation imports; hosted shell helpers remain canonical facade exports but are not invoked by the smoke spec |
| MCP SDK transport family facades | `std.nogc_async_mut.mcp_sdk.transport.*`, `std.gc_async_mut.mcp_sdk.transport.*` | `test/unit/lib/*/mcp_sdk/transport/mcp_sdk_transport_facade_spec.spl` validates stdio framing mode state and Content-Length header construction through each runtime family; extern-backed stdin/stdout read/write paths are syntax/import covered |
| MC/DC coverage parity | `std.nogc_async_mut.mcdc`, `std.gc_async_mut.mcdc` | `bin/simple check src/lib/nogc_async_mut/mcdc.spl src/lib/gc_async_mut/mcdc.spl` validates MC/DC coverage tracking and analysis helpers parse through each runtime family |
| Message transfer parity | `std.nogc_async_mut.message_transfer`, `std.gc_async_mut.message_transfer` | `bin/simple check src/lib/nogc_async_mut/message_transfer.spl src/lib/gc_async_mut/message_transfer.spl` validates actor message transfer helpers parse through each runtime family |
| Mem tracker package parity | `std.nogc_async_mut.mem_tracker.*`, `std.gc_async_mut.mem_tracker.*` | `bin/simple check src/lib/nogc_async_mut/mem_tracker/*.spl src/lib/gc_async_mut/mem_tracker/*.spl` validates mem-track extern wrappers and report types parse through each runtime family |
| Mimalloc package parity | `std.nogc_async_mut.{mimalloc,mimalloc_types,mimalloc_page,mimalloc_page_policy,mimalloc_stats,mimalloc_secure,mimalloc_tls}`, `std.gc_async_mut.*` | `bin/simple check src/lib/nogc_async_mut/mimalloc*.spl src/lib/gc_async_mut/mimalloc*.spl` validates pure Mimalloc page, policy, stats, secure, TLS, and allocator modules parse through each runtime family; internal imports are rewritten to each owning family |
| Net package parity | `std.nogc_async_mut.net.*`, `std.gc_async_mut.net.*` | `bin/simple check src/lib/nogc_async_mut/net/*.spl src/lib/gc_async_mut/net/*.spl` validates TCP, UDP, Telnet, HTTP, FFI, and package example modules parse through each runtime family; socket behavior remains extern-backed |
| Net root facade parity | `std.nogc_async_mut.net`, `std.gc_async_mut.net` | `bin/simple check src/lib/nogc_async_mut/net.spl src/lib/gc_async_mut/net.spl` validates the network facade module parses through each runtime family |
| HTTP root/server helper parity | `std.nogc_async_mut.http.*`, `std.gc_async_mut.http.*`, `std.nogc_async_mut.http_server.*`, `std.gc_async_mut.http_server.*` | `bin/simple check` over copied root HTTP helpers plus `http_server/{handler,middleware,response,router,types,utilities}.spl` validates accept-encoding, common parsing, cookies, headers, problem responses, request/response, type, URL, routing, middleware, handler, and utility helpers parse through each runtime family; `http_server` platform imports are rewritten where present |
| HTTP client package parity | `std.nogc_async_mut.http_client.*`, `std.gc_async_mut.http_client.*` | `bin/simple check src/lib/nogc_async_mut/http_client/*.spl src/lib/gc_async_mut/http_client/*.spl` validates HTTP client connection, request, response, SSL, type, and utility modules parse through each runtime family |
| HTTP auth/H2/WebSocket package parity | `std.nogc_async_mut.http.{auth,h2,ws}.*`, `std.gc_async_mut.http.*` | `bin/simple check src/lib/nogc_async_mut/http/auth/*.spl src/lib/nogc_async_mut/http/auth/.spipe_matchers_http_auth_spec.spl src/lib/nogc_async_mut/http/h2/*.spl src/lib/nogc_async_mut/http/ws/*.spl src/lib/gc_async_mut/http/auth/*.spl src/lib/gc_async_mut/http/auth/.spipe_matchers_http_auth_spec.spl src/lib/gc_async_mut/http/h2/*.spl src/lib/gc_async_mut/http/ws/*.spl` validates HTTP Basic/Digest auth, HTTP/2 frame/parser/writer, and WebSocket frame/parser/writer helpers parse through each runtime family; auth spec module/import names are rewritten to each owning family |
| MQTT helper package parity | `std.nogc_async_mut.mqtt.*`, `std.gc_async_mut.mqtt.*` | `bin/simple check src/lib/nogc_async_mut/mqtt/*.spl src/lib/gc_async_mut/mqtt/*.spl` validates MQTT connect, packet, publish, subscribe, type, and utility helpers parse through each runtime family |
| LSP package parity | `std.nogc_async_mut.lsp.*`, `std.gc_async_mut.lsp.*` | `bin/simple check src/lib/nogc_async_mut/lsp/*.spl src/lib/nogc_async_mut/lsp/handlers/*.spl src/lib/gc_async_mut/lsp/*.spl src/lib/gc_async_mut/lsp/handlers/*.spl` validates protocol, transport, parser, query, render, handler, position-query, and visibility modules parse through each runtime family; hardcoded package imports are rewritten to each owning family |
| IO runtime wrapper parity | `std.nogc_async_mut.{io,io_runtime,intrinsics}`, `std.gc_async_mut.*`, `std.nogc_async_mut.io.*`, `std.gc_async_mut.io.*` | `bin/simple check` over root IO facades, `io_runtime`, `intrinsics`, and copied IO wrapper modules validates file/env/process/time/regex/crypto/compression/audio/graphics/window/volatile and related runtime FFI surfaces parse through each runtime family; internal IO imports are rewritten to each owning family, and GC async receives the async file/TCP/UDP/buffer modules from `nogc_async_mut` |
| Log facade parity | `std.nogc_async_mut.log`, `std.gc_async_mut.log` | `bin/simple check src/lib/nogc_async_mut/log.spl src/lib/gc_async_mut/log.spl` validates runtime-guarded logging facade parsing through each runtime family |
| Lazy value parity | `std.nogc_async_mut.lazy_val`, `std.gc_async_mut.lazy_val` | `bin/simple check src/lib/nogc_async_mut/lazy_val.spl src/lib/gc_async_mut/lazy_val.spl` validates lazy-state and memoization helpers parse through each runtime family |
| Kafka helper package parity | `std.nogc_async_mut.kafka.*`, `std.gc_async_mut.kafka.*` | `bin/simple check src/lib/nogc_async_mut/kafka/*.spl src/lib/gc_async_mut/kafka/*.spl` validates Kafka producer, consumer, protocol, serialization, type, and utility helpers parse through each runtime family |
| JSON parser utility parity | `std.nogc_async_mut.json_parser_utils`, `std.gc_async_mut.json_parser_utils` | `bin/simple check src/lib/nogc_async_mut/json_parser_utils.spl src/lib/gc_async_mut/json_parser_utils.spl` validates JSON parser helpers parse through each runtime family |
| JIT package parity | `std.nogc_async_mut.jit.*`, `std.gc_async_mut.jit.*` | `bin/simple check src/lib/nogc_async_mut/jit/*.spl src/lib/gc_async_mut/jit/*.spl` validates JIT backend, HAL, layout, runner, type, utility, and root modules parse through each runtime family; JIT and debug-remote imports are rewritten to each owning family |
| JS engine package parity | `std.nogc_async_mut.js.engine.*`, `std.gc_async_mut.js.engine.*` | `bin/simple check src/lib/nogc_async_mut/js/engine/*.spl src/lib/gc_async_mut/js/engine/*.spl src/lib/nogc_async_mut/js/conformance/runner.spl src/lib/gc_async_mut/js/conformance/runner.spl` validates JS interpreter and conformance runner modules parse through each runtime family; interpreter imports are rewritten to each owning family |
| RV64 hardware pipeline parity | `std.nogc_async_mut.hardware.rv64.*`, `std.gc_async_mut.hardware.rv64.*` | `bin/simple check src/lib/nogc_async_mut/hardware/rv64/__init__.spl src/lib/nogc_async_mut/hardware/rv64/pipeline/*.spl src/lib/gc_async_mut/hardware/rv64/__init__.spl src/lib/gc_async_mut/hardware/rv64/pipeline/*.spl` validates RV64 pipeline stage helpers parse through each runtime family |
| Hardware package root parity | `std.nogc_async_mut.hardware`, `std.gc_async_mut.hardware` | `bin/simple check src/lib/nogc_async_mut/hardware/__init__.spl src/lib/gc_async_mut/hardware/__init__.spl` validates the hardware package root parses through each runtime family |
| Fuzz utility parity | `std.nogc_async_mut.fuzz`, `std.gc_async_mut.fuzz` | `bin/simple check src/lib/nogc_async_mut/fuzz.spl src/lib/gc_async_mut/fuzz.spl` validates fuzz helper parsing through each runtime family |
| FTP utility parity | `std.nogc_async_mut.ftp_utils`, `std.gc_async_mut.ftp_utils` | `bin/simple check src/lib/nogc_async_mut/ftp_utils.spl src/lib/gc_async_mut/ftp_utils.spl` validates FTP utility parsing through each runtime family; platform imports are rewritten to each owning family |
| Filesystem root parity | `std.nogc_async_mut.{fs,fs.path}`, `std.gc_async_mut.{fs,fs.path}` | `bin/simple check src/lib/nogc_async_mut/fs.spl src/lib/nogc_async_mut/fs/{__init__,path}.spl src/lib/gc_async_mut/fs.spl src/lib/gc_async_mut/fs/{__init__,path}.spl` validates filesystem root/path helpers parse through each runtime family; path imports are rewritten to each owning family |
| File system mock package parity | `std.nogc_async_mut.file_system.*`, `std.gc_async_mut.file_system.*` | `bin/simple check src/lib/nogc_async_mut/file_system/*.spl src/lib/gc_async_mut/file_system/*.spl` validates pure/mock-backed file, directory, metadata, path, permission, type, utility, and watch helpers parse through each runtime family |
| FFI package parity | `std.nogc_async_mut.ffi.*`, `std.gc_async_mut.ffi.*` | `bin/simple check src/lib/nogc_async_mut/ffi/*.spl src/lib/gc_async_mut/ffi/*.spl` validates runtime, system, CLI, IO, dynamic loading, LLVM, codegen, package, AST, coverage, and error FFI wrappers parse through each runtime family; intra-FFI imports are rewritten to each owning family |
| Failsafe package parity | `std.nogc_async_mut.failsafe.*`, `std.gc_async_mut.failsafe.*` | `bin/simple check src/lib/nogc_async_mut/failsafe/*.spl src/lib/gc_async_mut/failsafe/*.spl` validates failsafe core, panic, ratelimit, circuit, timeout, resource monitor, and package exports parse through each runtime family |
| Environment package parity | `std.nogc_async_mut.env.*`, `std.gc_async_mut.env.*` | `bin/simple check src/lib/nogc_async_mut/env/*.spl src/lib/gc_async_mut/env/*.spl` validates environment config, path, platform, variable, validation, type, and utility helpers parse through each runtime family; package-local env imports are rewritten to each owning family |
| Benchmark example parity | `std.nogc_async_mut.examples.benchmarks.*`, `std.gc_async_mut.examples.benchmarks.*` | `bin/simple check src/lib/nogc_async_mut/examples/benchmarks/*.spl src/lib/gc_async_mut/examples/benchmarks/*.spl` validates benchmark example modules parse through each runtime family |
| Gzip utility parity | `std.nogc_async_mut.gzip_utils`, `std.gc_async_mut.gzip_utils` | `bin/simple check src/lib/nogc_async_mut/gzip_utils.spl src/lib/gc_async_mut/gzip_utils.spl` validates gzip helper parsing through each runtime family |
| GPU driver package parity | `std.nogc_async_mut.gpu_driver.*`, `std.gc_async_mut.gpu_driver.*` | `bin/simple check src/lib/nogc_async_mut/gpu_driver/*.spl src/lib/gc_async_mut/gpu_driver/*.spl` validates CUDA driver wrappers and driver registry adapter parse through each runtime family; package imports are rewritten to each owning family and remain local runtime externs rather than compiler-loader dependencies |
| GPU runtime package parity | `std.nogc_async_mut.gpu_runtime.*`, `std.gc_async_mut.gpu_runtime.*` | `bin/simple check src/lib/nogc_async_mut/gpu_runtime/*.spl src/lib/gc_async_mut/gpu_runtime/*.spl` validates GPU runtime helpers parse through each runtime family; Torch imports are rewritten to each owning family |
| Glob utility parity | `std.nogc_async_mut.glob`, `std.gc_async_mut.glob` | `bin/simple check src/lib/nogc_async_mut/glob.spl src/lib/gc_async_mut/glob.spl` validates glob helpers parse through each runtime family |
| GC runtime helper parity | `std.nogc_async_mut.gc`, `std.gc_async_mut.gc` | `bin/simple check src/lib/nogc_async_mut/gc.spl src/lib/gc_async_mut/gc.spl` validates GC helper parsing through each runtime family; atomic imports are rewritten to each owning family |
| HTML parser utility parity | `std.nogc_async_mut.html_parser_utils`, `std.gc_async_mut.html_parser_utils` | `bin/simple check src/lib/nogc_async_mut/html_parser_utils.spl src/lib/gc_async_mut/html_parser_utils.spl` validates HTML parser helpers parse through each runtime family |
| LLM notification parity | `std.nogc_async_mut.llm.notify`, `std.gc_async_mut.llm.notify` | `bin/simple check src/lib/nogc_async_mut/llm/notify.spl src/lib/gc_async_mut/llm/notify.spl` validates notification audit/record adapter parsing through each runtime family after IO imports are rewritten to each owning family |
| OAuth2 client-credentials parity | `std.nogc_async_mut.oauth2`, `std.gc_async_mut.oauth2` | `bin/simple check src/lib/nogc_async_mut/oauth2.spl src/lib/gc_async_mut/oauth2.spl` validates OAuth2 token/cache helper parsing through each runtime family; HTTP and filesystem operations remain canonical to the no-GC sync implementation |
| SDoctest test-runner family facades | `std.nogc_async_mut.test_runner.sdoctest.*`, `std.gc_async_mut.test_runner.sdoctest.*` | `test/unit/lib/*/test_runner/sdoctest/sdoctest_facade_spec.spl` validates config, fence parsing, glob matching, block/result records, and result helpers; `test/unit/app/sdoctest_spec.spl` covers canonical extractor behavior |
| Source tooling family facades | `std.nogc_async_mut.src.tooling.*`, `std.gc_async_mut.src.tooling.*` | `test/unit/lib/*/src/tooling/tooling_facade_spec.spl` validates regex helper and easy-fix record imports; `test/unit/app/tooling/regex_utils_spec.spl` covers canonical regex utility behavior |
| Source core family facades | `std.nogc_async_mut.src.core.*`, `std.gc_async_mut.src.core.*` | `test/unit/lib/*/src/core/src_core_facade_spec.spl` validates context managers, decorator records, random state/range helpers, regex helpers, and synchronization primitives; exact subtree parity is maintained against `nogc_sync_mut/src/core` |
| Source collections family facades | `std.nogc_async_mut.src.collections.*`, `std.gc_async_mut.src.collections.*` | `test/unit/lib/*/src/collections/src_collections_facade_spec.spl` validates pure HashMap, HashSet, and BTreeMap behavior; canonical map/tree mutation paths are interpreter-safe |
| Source DL family facades | `std.nogc_async_mut.src.dl.*`, `std.gc_async_mut.src.dl.*` | `test/unit/lib/*/src/dl/src_dl_facade_spec.spl` validates dtype/device/backend helpers, default DL config, and config parser helpers through each runtime family; file-backed config loading remains syntax/import covered |
| Source math family facades | `std.nogc_async_mut.src.math.*`, `std.gc_async_mut.src.math.*` | `test/unit/lib/*/src/math/src_math_facade_spec.spl` validates backend availability, backend/render-format labels, backend capability records, and explicit CPU selection; generic expression rendering helpers are syntax/import covered |
| Source tensor factory facades | `std.nogc_async_mut.src.tensor.*`, `std.gc_async_mut.src.tensor.*` | `test/unit/lib/*/src/tensor/src_tensor_facade_spec.spl` validates tensor factory API export coverage through each runtime family; backend tensor allocation paths are syntax/import covered, and canonical tensor init now re-exports factory symbols explicitly |
| Play CDP family facades | `std.nogc_async_mut.play.cdp.*`, `std.gc_async_mut.play.cdp.*` | `test/unit/lib/*/play/cdp/play_cdp_facade_spec.spl` validates pure WebSocket URL/frame parsing, CDP constants, and modifier helpers through each runtime family; live socket/session paths are syntax/import covered and currently emit pre-existing common/net interpreter diagnostics |
| Play automation package parity | `std.nogc_async_mut.play.{types,launcher,page,locator,keyboard,mouse,expect,electron_application,sdl2_backend,trace,xvfb,mod,wm.mod}`, `std.gc_async_mut.play.*` | `bin/simple check src/lib/nogc_async_mut/play/*.spl src/lib/gc_async_mut/play/*.spl src/lib/nogc_async_mut/play/wm/*.spl src/lib/gc_async_mut/play/wm/*.spl` validates non-CDP play automation modules parse through each runtime family; live process/display behavior remains canonical to the no-GC sync implementation |
| Path utility parity | `std.nogc_async_mut.path`, `std.gc_async_mut.path` | `bin/simple check src/lib/nogc_async_mut/path.spl src/lib/gc_async_mut/path.spl` validates pure path utility parsing through each runtime family; platform package imports now point at the owning family path surface |
| Package tooling parity | `std.nogc_async_mut.package.*`, `std.gc_async_mut.package.*` | `bin/simple check src/lib/nogc_async_mut/package/*.spl src/lib/gc_async_mut/package/*.spl src/lib/nogc_async_mut/package/installer/*.spl src/lib/gc_async_mut/package/installer/*.spl` validates package manifest, lockfile, semver, install/list/build/dist/smoke/FFI test helpers, and installer backends through each runtime family; installer imports are rewritten to each owning family |
| Package FFI parity | `std.nogc_async_mut.package_ffi`, `std.gc_async_mut.package_ffi` | `bin/simple check src/lib/nogc_async_mut/package_ffi.spl src/lib/gc_async_mut/package_ffi.spl` validates package FFI wrapper parsing through each runtime family |
| OIDC package parity | `std.nogc_async_mut.oidc.*`, `std.gc_async_mut.oidc.*` | `bin/simple check src/lib/nogc_async_mut/oidc/*.spl src/lib/gc_async_mut/oidc/*.spl` validates OpenID discovery and ID-token validation helpers parse through each runtime family; HTTP/JWT behavior remains canonical to the no-GC sync implementation |
| OAuth helper package parity | `std.nogc_async_mut.oauth.*`, `std.gc_async_mut.oauth.*` | `bin/simple check src/lib/nogc_async_mut/oauth/*.spl src/lib/gc_async_mut/oauth/*.spl` validates authorization URL, token, refresh, type, validation, and utility helpers parse through each runtime family |
| Perf configuration parity | `std.nogc_async_mut.perf`, `std.gc_async_mut.perf` | `bin/simple check src/lib/nogc_async_mut/perf.spl src/lib/gc_async_mut/perf.spl` validates performance configuration/statistics helpers parse through each runtime family |
| Pointer ownership package parity | `std.nogc_async_mut.ptr.*`, `std.gc_async_mut.ptr.*` | `bin/simple check src/lib/nogc_async_mut/ptr/*.spl src/lib/gc_async_mut/ptr/*.spl` validates handle, unique, weak, and pointer-state modules parse through each runtime family; package imports are rewritten to each owning family while canonical no-GC sync specs own behavior |
| Platform package parity | `std.nogc_async_mut.platform.*`, `std.gc_async_mut.platform.*` | `bin/simple check src/lib/nogc_async_mut/platform/*.spl src/lib/gc_async_mut/platform/*.spl` validates config, conversion, linker, newline, text I/O, wire, and platform aggregate parsing through each runtime family; internal imports are rewritten to each owning family |
| Platform root helper parity | `std.nogc_async_mut.platform`, `std.gc_async_mut.platform` | `bin/simple check src/lib/nogc_async_mut/platform.spl src/lib/gc_async_mut/platform.spl` validates the root platform detection/path helper parses through each runtime family; path imports are rewritten to each owning family |
| Privilege filesystem store parity | `std.nogc_async_mut.privilege.store_fs`, `std.gc_async_mut.privilege.store_fs` | `bin/simple check src/lib/nogc_async_mut/privilege/store_fs.spl src/lib/gc_async_mut/privilege/store_fs.spl` validates disk-backed privilege-store persistence parsing through each runtime family; common privilege store specs own behavior |
| Process resource helper parity | `std.nogc_async_mut.{process_monitor,process_limits}`, `std.gc_async_mut.{process_monitor,process_limits}` | `bin/simple check src/lib/nogc_async_mut/process_monitor.spl src/lib/gc_async_mut/process_monitor.spl src/lib/nogc_async_mut/process_limits.spl src/lib/gc_async_mut/process_limits.spl` validates hosted process metrics and resource-profile helper parsing through each runtime family; dependency-boundary guard remains the POSIX/process marker policy gate |
| QEMU QMP client parity | `std.nogc_async_mut.qemu.*`, `std.gc_async_mut.qemu.*` | `bin/simple check src/lib/nogc_async_mut/qemu/*.spl src/lib/gc_async_mut/qemu/*.spl` validates hosted QMP client package parsing through each runtime family; Unix-socket behavior remains canonical to the no-GC sync implementation |
| Reference-counting parity | `std.nogc_async_mut.rc`, `std.gc_async_mut.rc` | `bin/simple check src/lib/nogc_async_mut/rc.spl src/lib/gc_async_mut/rc.spl` validates Rc/Arc/Weak wrapper parsing through each runtime family; runtime extern behavior remains canonical to the no-GC sync implementation |
| Security enforcement family facades | `std.nogc_async_mut.security.enforcement.*`, `std.gc_async_mut.security.enforcement.*` | `test/unit/lib/*/security/enforcement/security_enforcement_facade_spec.spl` validates capability parsing/matching and resolver result helpers through each runtime family; audit-integrated gate paths are syntax/import covered |
| Security validation family facades | `std.nogc_async_mut.security.validation.*`, `std.gc_async_mut.security.validation.*` | `test/unit/lib/*/security/validation/security_validation_facade_spec.spl` validates prompt sanitization, delimiter wrapping, canary leakage checks, URL scheme/host validation, private IP detection, and localhost detection through each runtime family; canonical prompt pattern removal now preserves safe input casing |
| Security core/auth package parity | `std.nogc_async_mut.security.{types,sanitize,audit_log,audit_chain,mod}`, `std.gc_async_mut.security.*`, `std.nogc_async_mut.security.auth.*`, `std.gc_async_mut.security.auth.*` | `bin/simple check src/lib/nogc_async_mut/security/*.spl src/lib/gc_async_mut/security/*.spl src/lib/nogc_async_mut/security/auth/*.spl src/lib/gc_async_mut/security/auth/*.spl` validates security core and auth package parsing through each runtime family; canonical security specs own behavior |
| Shell environment package parity | `std.nogc_async_mut.shell.*`, `std.gc_async_mut.shell.*` | `bin/simple check src/lib/nogc_async_mut/shell/*.spl src/lib/gc_async_mut/shell/*.spl` validates hosted env/cwd package parsing through each runtime family; dependency-boundary guard remains the POSIX/process marker policy gate |
| SIMD package parity | `std.nogc_async_mut.simd.*`, `std.gc_async_mut.simd.*` | `bin/simple check src/lib/nogc_async_mut/simd/*.spl src/lib/gc_async_mut/simd/*.spl` validates vector, fixed/scalable, mask, alias, mod, and profile modules parse through each runtime family; canonical `test/unit/lib/simd/*_spec.spl` owns behavior |
| SIMD intrinsic aggregate parity | `std.nogc_async_mut.simd`, `std.gc_async_mut.simd` | `bin/simple check src/lib/nogc_async_mut/simd.spl src/lib/gc_async_mut/simd.spl` validates the top-level intrinsic aggregate parses through each runtime family; canonical `test/feature/scilib/simd_f32_spec.spl` and `test/unit/lib/simd/*_spec.spl` own behavior |
| ASan sanitizer family facades | `std.nogc_async_mut.sanitizer.asan.*`, `std.gc_async_mut.sanitizer.asan.*` | `test/unit/lib/*/sanitizer/asan/asan_facade_spec.spl` validates enable/reset state, allocation tracking, bounds errors, use-after-free, double-free event capture, and allocation records through each runtime family; canonical ASan now imports shared sanitizer event types explicitly |
| UBSan sanitizer family facades | `std.nogc_async_mut.sanitizer.ubsan.*`, `std.gc_async_mut.sanitizer.ubsan.*` | `test/unit/lib/*/sanitizer/ubsan/ubsan_facade_spec.spl` validates enable/reset state, nil/division/index checks, event capture, and violation records through each runtime family; canonical UBSan now imports shared sanitizer event types explicitly |
| TSan sanitizer family facades | `std.nogc_async_mut.sanitizer.tsan.*`, `std.gc_async_mut.sanitizer.tsan.*` | `test/unit/lib/*/sanitizer/tsan/tsan_facade_spec.spl` validates enable/reset state, cross-thread race detection, lock-order event capture, and data-race records through each runtime family; canonical TSan now imports shared sanitizer event types explicitly |
| MSan sanitizer family facades | `std.nogc_async_mut.sanitizer.msan.*`, `std.gc_async_mut.sanitizer.msan.*` | `test/unit/lib/*/sanitizer/msan/msan_facade_spec.spl` validates enable/reset state, initialization checks, use-after-free event capture, overlap checks, and memory-region records through each runtime family; canonical MSan now imports shared sanitizer event types explicitly |
| LSan sanitizer family facades | `std.nogc_async_mut.sanitizer.lsan.*`, `std.gc_async_mut.sanitizer.lsan.*` | `test/unit/lib/*/sanitizer/lsan/lsan_facade_spec.spl` validates disabled-state checks, suppression tags, and leak-checkpoint records through each runtime family; mem-tracker-backed enable/checkpoint paths are syntax/import covered because interpreter mode lacks the mem-tracker extern |
| Sanitizer root package parity | `std.nogc_async_mut.sanitizer.{types,mod,__init__}`, `std.gc_async_mut.sanitizer.*` | `bin/simple check src/lib/nogc_async_mut/sanitizer/{__init__.spl,mod.spl,types.spl} src/lib/gc_async_mut/sanitizer/{__init__.spl,mod.spl,types.spl}` validates shared sanitizer event types and unified API package parsing through each runtime family |
| Security aspect family facades | `std.nogc_async_mut.security.aspects.*`, `std.gc_async_mut.security.aspects.*` | `test/unit/lib/*/security/aspects/security_aspects_facade_spec.spl` validates side-effect-free audit/auth/validation helper imports through compiler join-point context; full advice side effects remain syntax-checked |
| Service daemon package parity | `std.nogc_async_mut.service.*`, `std.gc_async_mut.service.*` | `bin/simple check src/lib/nogc_async_mut/service/*.spl src/lib/gc_async_mut/service/*.spl` validates hosted service lifecycle, lease, queue, audit, daemon, extern, and trait modules parse through each runtime family; dependency-boundary guard remains the host/process marker policy gate |
| DAP adapter family facades | `std.nogc_async_mut.dap.adapter.*`, `std.gc_async_mut.dap.adapter.*` | `test/unit/lib/*/dap/adapter/dap_adapter_facade_spec.spl` validates adapter config/capabilities, LLDB-DAP framing/JSON helpers, and ST-Link hex parsing; hosted adapter class wrappers are syntax-checked |
| DAP root package parity | `std.nogc_async_mut.dap.*`, `std.gc_async_mut.dap.*` | `bin/simple check src/lib/nogc_async_mut/dap/*.spl src/lib/gc_async_mut/dap/*.spl` validates breakpoints, handlers, types, hooks, main, protocol, server, and transport modules parse through each runtime family; adapter subtree parity is tracked separately |
| Daemon SDK package parity | `std.nogc_async_mut.daemon_sdk.*`, `std.gc_async_mut.daemon_sdk.*` | `bin/simple check src/lib/nogc_async_mut/daemon_sdk/*.spl src/lib/gc_async_mut/daemon_sdk/*.spl` validates client, daemon loop, lock, protocol, type, and root modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/daemon_sdk` |
| DNS packet package parity | `std.nogc_async_mut.dns.*`, `std.gc_async_mut.dns.*` | `bin/simple check src/lib/nogc_async_mut/dns/*.spl src/lib/gc_async_mut/dns/*.spl` validates DNS build, parse, query, resolve, type, and utility modules parse through each runtime family; `std.nogc_async_mut.dns.resolver` remains an async-only extra and imports the local DNS packet modules |
| Dig utility module parity | `std.nogc_async_mut.dig`, `std.gc_async_mut.dig` | `bin/simple check src/lib/nogc_async_mut/dig.spl src/lib/gc_async_mut/dig.spl` validates the pure dig helper module parses through each runtime family |
| Diagram package parity | `std.nogc_async_mut.diagram`, `std.gc_async_mut.diagram` | `bin/simple check src/lib/nogc_async_mut/diagram/*.spl src/lib/gc_async_mut/diagram/*.spl` validates the diagram package root parses through each runtime family |
| DataFrame package parity | `std.nogc_async_mut.df.*`, `std.gc_async_mut.df.*` | `bin/simple check src/lib/nogc_async_mut/df/*.spl src/lib/gc_async_mut/df/*.spl` validates DataFrame core, I/O, and transform modules parse through each runtime family; local DataFrame imports are rewritten to each owning family |
| Database root package parity | `std.nogc_async_mut.database.*`, `std.gc_async_mut.database.*` | `bin/simple check src/lib/nogc_async_mut/database/*.spl src/lib/gc_async_mut/database/*.spl` validates atomic file helpers, SDN core/query/checker modules, bug/feature/task/todo/requirement tracking, WAL, FTS, metrics, registry, and root exports parse through each runtime family; root self-imports are rewritten to each owning family |
| Config and coverage module parity | `std.nogc_async_mut.{conf,config_parser,coverage}`, `std.gc_async_mut.{conf,config_parser,coverage}` | `bin/simple check src/lib/nogc_async_mut/coverage.spl src/lib/gc_async_mut/coverage.spl src/lib/nogc_async_mut/conf.spl src/lib/gc_async_mut/conf.spl src/lib/nogc_async_mut/config_parser.spl src/lib/gc_async_mut/config_parser.spl` validates config parsing/loading and coverage data helpers parse through each runtime family |
| CLI package parity | `std.nogc_async_mut.cli.*`, `std.gc_async_mut.cli.*` | `bin/simple check src/lib/nogc_async_mut/cli/*.spl src/lib/gc_async_mut/cli/*.spl` validates CLI parser, utility, formatting, package utility, parser loader, standalone parser, type, and root modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/cli` |
| Compositor package parity | `std.nogc_async_mut.compositor.*`, `std.gc_async_mut.compositor.*` | `bin/simple check src/lib/nogc_async_mut/compositor/*.spl src/lib/gc_async_mut/compositor/*.spl` validates damage, frame, GPU command/surface, layer, rasterizer, scroll, stacking, and tile modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/compositor` |
| Debug root package parity | `std.nogc_async_mut.debug.*`, `std.gc_async_mut.debug.*` | `bin/simple check src/lib/nogc_async_mut/debug/*.spl src/lib/gc_async_mut/debug/*.spl` validates debug info bridge, interpreter backend, native agent, and SMF agent modules parse through each runtime family; `std.nogc_async_mut.debug.coordinator` remains an async-only extra |
| Debug format package parity | `std.nogc_async_mut.debug.formats.*`, `std.gc_async_mut.debug.formats.*` | `bin/simple check src/lib/nogc_async_mut/debug/formats/*.spl src/lib/gc_async_mut/debug/formats/*.spl` plus `bin/simple check src/lib/*/debug/formats/test/*.spl src/lib/*/debug/formats/test/.spipe_matchers*.spl` validates DWARF, PDB/MSF, CodeView, dSYM, debug provider/type modules, format specs, and SPipe matcher helpers through each runtime family; debug remote/spec imports are rewritten to each owning family |
| Debug remote package parity | `std.nogc_async_mut.debug.remote.*`, `std.gc_async_mut.debug.remote.*` | `find src/lib/nogc_async_mut/debug/remote src/lib/gc_async_mut/debug/remote -type f -name '*.spl' -print0 \| xargs -0 bin/simple check` validates remote debug backends, protocols, targets, feature registry, hardware replay, remote execution lanes, TRACE32 FFI helpers, and QEMU runner modules parse through each runtime family; `nogc_sync_mut` imports are rewritten to each owning family |
| Debugger and DB atomic module parity | `std.nogc_async_mut.debugger`, `std.gc_async_mut.debugger`, `std.nogc_async_mut.db_atomic`, `std.gc_async_mut.db_atomic` | `bin/simple check src/lib/nogc_async_mut/debugger.spl src/lib/gc_async_mut/debugger.spl src/lib/nogc_async_mut/db_atomic.spl src/lib/gc_async_mut/db_atomic.spl` validates the top-level debugger facade and DB atomic helper parse through each runtime family |
| Desktop integration package parity | `std.nogc_async_mut.desktop.*`, `std.gc_async_mut.desktop.*` | `bin/simple check src/lib/nogc_async_mut/desktop/*.spl src/lib/gc_async_mut/desktop/*.spl` validates clipboard, dialogs, display, shortcuts, lifecycle, notifications, power, protocol, shell-open, tray, and updater modules parse through each runtime family; hosted FFI/window/web-ui imports are rewritten to each owning family |
| Dependency tracker package parity | `std.nogc_async_mut.dependency_tracker.*`, `std.gc_async_mut.dependency_tracker.*` | `bin/simple check src/lib/nogc_async_mut/dependency_tracker/*.spl src/lib/gc_async_mut/dependency_tracker/*.spl` validates graph, macro import, resolution, symbol, and visibility helpers parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/dependency_tracker` |
| Engine audio family facades | `std.nogc_async_mut.engine.audio.*`, `std.gc_async_mut.engine.audio.*` | `test/unit/lib/*/engine/audio/engine_audio_facade_spec.spl` validates audio defaults, handles, Doppler, effect chains, audio groups, and mixer snapshots; audio manager backend wrapper is syntax-checked |
| Engine AI family facades | `std.nogc_async_mut.engine.ai.*`, `std.gc_async_mut.engine.ai.*` | `test/unit/lib/*/engine/ai/engine_ai_facade_spec.spl` validates navmesh point distance, polygon center/membership, neighbor linking, polygon lookup, and simple pathfinding through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/engine/ai` |
| Engine core family facades | `std.nogc_async_mut.engine.core.*`, `std.gc_async_mut.engine.core.*` | `test/unit/lib/*/engine/core/engine_core_facade_spec.spl` validates clock, console, object pool, coroutine helper, profiler imports, and the shared `renderer_mode` enum; hosted game-loop/engine wrappers are syntax-checked, existing GC `engine.spl` remains an extra GC-only engine surface, and no-GC game loops import the owning-family renderer mode instead of reaching into GC async |
| Engine component family facades | `std.nogc_async_mut.engine.component.*`, `std.gc_async_mut.engine.component.*` | `test/unit/lib/*/engine/component/engine_component_facade_spec.spl` validates 2D/3D component records, enum helpers, mesh helper imports, registry imports, and camera/tilemap extension wrappers; canonical 2D registry mutation behavior has an existing tracked failure |
| Engine build family facades | `std.nogc_async_mut.engine.build.*`, `std.gc_async_mut.engine.build.*` | `test/unit/lib/*/engine/build/engine_build_facade_spec.spl` validates build targets, asset bundle accounting/filtering, pipeline steps, simulated build results, and error records through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/engine/build` |
| Engine scene family facades | `std.nogc_async_mut.engine.scene.*`, `std.gc_async_mut.engine.scene.*` | `test/unit/lib/*/engine/scene/engine_scene_facade_spec.spl` validates 2D/3D node records, tree queries, serialization helpers, scene manager handles, and prefab records; exact subtree parity is maintained against `nogc_sync_mut/engine/scene` |
| Engine resource family facades | `std.nogc_async_mut.engine.resource.*`, `std.gc_async_mut.engine.resource.*` | `test/unit/lib/*/engine/resource/engine_resource_facade_spec.spl` validates generic handles, resource state/type enums, resource manager construction, scriptable object records, and glTF document/type imports; exact subtree parity is maintained against `nogc_sync_mut/engine/resource` |
| Engine input family facades | `std.nogc_async_mut.engine.input.*`, `std.gc_async_mut.engine.input.*` | `test/unit/lib/*/engine/input/engine_input_facade_spec.spl` validates pure input states, mouse defaults, direct action binding, and query helpers through each runtime family; FFI polling and default-binding helper mutation remain syntax/import covered |
| Engine UI family facades | `std.nogc_async_mut.engine.ui.*`, `std.gc_async_mut.engine.ui.*` | `test/unit/lib/*/engine/ui/engine_ui_facade_spec.spl` validates canvas element mutation, visibility, lookup, rect computation, anchors, and widget constructors through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/engine/ui` |
| Engine package root parity | `std.nogc_async_mut.engine`, `std.gc_async_mut.engine` | `bin/simple check src/lib/nogc_async_mut/engine/{__init__,mod}.spl src/lib/gc_async_mut/engine/{__init__,mod}.spl` validates the engine package root and module export surface parse through each runtime family |
| Engine scripting family facades | `std.nogc_async_mut.engine.scripting.*`, `std.gc_async_mut.engine.scripting.*` | `test/unit/lib/*/engine/scripting/engine_scripting_facade_spec.spl` validates visual graph node/connection helpers and built-in visual scripting node constructors through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/engine/scripting` |
| Engine LLM family facades | `std.nogc_async_mut.engine.llm.*`, `std.gc_async_mut.engine.llm.*` | `test/unit/lib/*/engine/llm/engine_llm_facade_spec.spl` validates command dispatch records, context packer records, scene/debug helpers, code generator records, and asset suggester records; exact subtree parity is maintained against `nogc_sync_mut/engine/llm` |
| Engine animation family facades | `std.nogc_async_mut.engine.animation.*`, `std.gc_async_mut.engine.animation.*` | `test/unit/lib/*/engine/animation/engine_animation_facade_spec.spl` validates skeleton, clip, blender, skinning, IK, and timeline records/helpers; exact subtree parity is maintained against `nogc_sync_mut/engine/animation` |
| Engine sprite family facades | `std.nogc_async_mut.engine.sprite.*`, `std.gc_async_mut.engine.sprite.*` | `test/unit/lib/*/engine/sprite/engine_sprite_facade_spec.spl` validates texture color helpers, atlas packing, sprite-sheet counters, animator defaults, and atlas-builder layout exports; exact subtree parity is maintained against `nogc_sync_mut/engine/sprite` |
| Engine net family facades | `std.nogc_async_mut.engine.net.*`, `std.gc_async_mut.engine.net.*` | `test/unit/lib/*/engine/net/engine_net_facade_spec.spl` validates server/client state, entity sync, and RPC dispatch records through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/engine/net` |
| Engine physics family facades | `std.nogc_async_mut.engine.physics.*`, `std.gc_async_mut.engine.physics.*` | `find src/lib/nogc_async_mut/engine/physics src/lib/gc_async_mut/engine/physics -type f -name '*.spl' -print0 \| xargs -0 bin/simple check` validates physics backends, broadphase, solver data, graph coloring/sleeping, ECS/render integration, narrowphase, queries, simple 2D/3D physics, constraints, vehicles, ragdoll, and world modules parse through each runtime family; physics/SIMD imports are rewritten to each owning family |
| Engine render family facades | `std.nogc_async_mut.engine.render.*`, `std.gc_async_mut.engine.render.*` | `find src/lib/nogc_async_mut/engine/render src/lib/gc_async_mut/engine/render -type f -name '*.spl' -print0 \| xargs -0 bin/simple check` validates 2D/3D render commands, materials, pipeline, text/font, sprites, shader source/compiler, Vulkan/WebGPU/software backends, renderer, texture/atlas, particles, lighting, terrain, skybox, and debug draw modules parse through each runtime family; render, component, sprite, IO, and physics imports are rewritten to each owning family, while existing GC-only GPU bridge/pipeline/cache/shader modules remain preserved as GC extras with GC-family imports |
| Experiment/testing helper parity | `std.nogc_async_mut.src.exp.*`, `std.gc_async_mut.src.exp.*`, `std.nogc_async_mut.src.testing.*`, `std.gc_async_mut.src.testing.*`, `std.nogc_async_mut.examples.testing.*`, `std.gc_async_mut.examples.testing.*` | `bin/simple check` over `src/exp`, `src/testing`, `src/testing/mock`, and `examples/testing` validates experiment tracking, mock/testing helpers, GPU test helpers, and testing examples parse through each runtime family; exact subtree parity is maintained against the canonical `nogc_sync_mut` helper trees |
| ECS package parity | `std.nogc_async_mut.ecs.*`, `std.gc_async_mut.ecs.*` | `bin/simple check src/lib/nogc_async_mut/ecs/*.spl src/lib/gc_async_mut/ecs/*.spl` validates entity, component store, query, system, world, and change detection modules parse through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/ecs` |
| Editor panel family facades | `std.nogc_async_mut.editor.panels.*`, `std.gc_async_mut.editor.panels.*` | `test/unit/lib/*/editor/panels/editor_panels_facade_spec.spl` validates hierarchy visibility, asset filtering, mixer state, and inspector section toggling through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/editor/panels` |
| Editor viewport parity | `std.nogc_async_mut.editor.viewport`, `std.gc_async_mut.editor.viewport` | `bin/simple check src/lib/nogc_async_mut/editor/viewport.spl src/lib/gc_async_mut/editor/viewport.spl` validates editor viewport helpers parse through each runtime family; editor mode imports are rewritten to each owning family |
| Editor root package parity | `std.nogc_async_mut.editor.*`, `std.gc_async_mut.editor.*` | `bin/simple check src/lib/nogc_async_mut/editor/*.spl src/lib/gc_async_mut/editor/*.spl` validates editor app, mode, panel, selection, viewport, gizmo, typed event bus, HTML template, and engine bridge modules parse through each runtime family; editor and drawing imports are rewritten to each owning family |
| Terminal power family facades | `std.nogc_async_mut.terminal.power.*`, `std.gc_async_mut.terminal.power.*` | `test/unit/lib/*/terminal/power/terminal_power_facade_spec.spl` validates hosted-safe relay and host backend imports; controller and TRACE32 wrappers are syntax-checked because interpreter import loads the hosted debug stack |
| NVFS raw/NVMe arena | `std.fs_driver.nvfs_arena` | `test/integration/storage/nvfs/nvfs_nvme_arena_spec.spl`, `test/integration/storage/nvfs/nvfs_remount_persistence_spec.spl`, and `test/system/kernel/nvfs_elf_load_spec.spl` no longer import NVFS examples |
| NVFS arena family facades | `std.nogc_async_mut.fs_driver.nvfs_arena`, `std.gc_async_mut.fs_driver.nvfs_arena` | `test/unit/lib/*/fs_driver/nvfs_backend_parity_spec.spl` validates facade exports and behavior |
| NVFS trait contract family facades | `std.nogc_async_mut.fs.nvfs.*`, `std.gc_async_mut.fs.nvfs.*` | `test/unit/lib/*/fs/nvfs/nvfs_facade_spec.spl` validates arena-handle aliases, extent records, and superblock headers through each runtime family; no POSIX imports are introduced |
| NVFS mount-table drivers | `std.fs_driver.nvfs_driver`, `std.fs_driver.nvfs_posix_driver` | `DriverInstance` no longer imports NVFS examples |
| NVFS driver family facades | `std.nogc_async_mut.fs_driver.nvfs_driver`, `std.gc_async_mut.fs_driver.nvfs_driver` | `test/unit/lib/*/fs_driver/nvfs_driver_facade_spec.spl` validates hosted construction through each family |
| fs_driver package facades | `std.nogc_async_mut.fs_driver`, `std.gc_async_mut.fs_driver` | `test/unit/lib/*/fs_driver/fs_driver_init_facade_spec.spl` validates core contracts plus NVFS helper exports |
| fs_driver root implementation parity | `std.nogc_async_mut.fs_driver.{direct_io,driver_adapter,extension,fat32_core,fat32_dir_ops,fat32_parsers,fat32_stub,fat32_test_device,instance,mount_table,ops,ramfs}`, `std.gc_async_mut.fs_driver.*` | `bin/simple check` over the copied root fs_driver implementation files validates direct I/O, FAT32, mount table, driver instance, ops, and RamFS modules parse through each runtime family |
| NVFS POSIX driver family facades | `std.nogc_async_mut.fs_driver.nvfs_posix_driver`, `std.gc_async_mut.fs_driver.nvfs_posix_driver` | thin `export use` wrappers backed by `std.nogc_sync_mut.fs_driver.nvfs_posix_driver` |
| NVFS superblock disk I/O | `std.fs_driver.nvfs_superblock` | `os.kernel.boot.boot_fs`, `test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl`, and `test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl` no longer import NVFS examples |
| NVFS superblock family facades | `std.nogc_async_mut.fs_driver.nvfs_superblock`, `std.gc_async_mut.fs_driver.nvfs_superblock` | parity specs validate facade exports for runtime-family consumers |
| NVFS storage/durability ordinals | `std.storage.nvfs_constants` | `test/system/simple_db_nvfs_constants_spec.spl` no longer imports NVFS examples |
| NVFS storage constants family facades | `std.nogc_async_mut.storage.nvfs_constants`, `std.gc_async_mut.storage.nvfs_constants` | thin `export use` wrappers backed by `std.nogc_sync_mut.storage.nvfs_constants` |
| Storage policy family facades | `std.nogc_async_mut.storage.{storage_class,durability,capability,arena,nvme_feature_policy}`, `std.gc_async_mut.storage.{storage_class,durability,capability,arena,nvme_feature_policy}` | `test/unit/lib/*/storage/storage_policy_facade_spec.spl` validates storage class, durability, arena handle, and NVMe policy exports |
| Storage MDSOC base header parity | `std.nogc_async_mut.storage.mdsoc_base`, `std.gc_async_mut.storage.mdsoc_base` | `bin/simple check src/lib/*/storage/mdsoc_base.spl` validates header-only runtime-family parity; no executable API exists yet |
| Shared storage primitive family facades | `std.nogc_async_mut.storage.shared.*`, `std.gc_async_mut.storage.shared.*` | `test/unit/lib/*/storage/shared/storage_shared_facade_spec.spl` validates WAL, B-tree, checkpoint ring, and intent-log imports through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/storage/shared` |
| SMTP helper package parity | `std.nogc_async_mut.smtp.*`, `std.gc_async_mut.smtp.*` | `bin/simple check src/lib/nogc_async_mut/smtp/*.spl src/lib/gc_async_mut/smtp/*.spl` validates pure SMTP command, auth, MIME, send, type, and encoding helpers parse through each runtime family; files are mechanical copies of the canonical no-GC sync package |
| Storage package facades | `std.nogc_async_mut.storage`, `std.gc_async_mut.storage` | `test/unit/lib/*/storage/storage_init_facade_spec.spl` validates package-level re-exports |
| STOMP family facades | `std.nogc_async_mut.stomp.*`, `std.gc_async_mut.stomp.*` | `test/unit/lib/*/stomp/stomp_facade_spec.spl` validates STOMP constants and heartbeat negotiation helpers through each runtime family; frame/message/subscribe utilities remain syntax/import covered |
| Simple DB interface facades | `std.nogc_async_mut.simple_db_if.*`, `std.gc_async_mut.simple_db_if.*` | `test/unit/lib/*/simple_db_if/simple_db_if_facade_spec.spl` validates DB interface value types and page buffer records through each runtime family; signature-only storage traits remain import covered |
| SPipe alias parity | `std.nogc_async_mut.spipe`, `std.gc_async_mut.spipe` | `bin/simple check src/lib/*/spipe.spl` validates the spec-alias module parses through each runtime family |
| SPipe framework facades | `std.nogc_async_mut.spec`, `std.gc_async_mut.spec` | `bin/simple check src/lib/nogc_async_mut/spec.spl src/lib/gc_async_mut/spec.spl` validates explicit test-framework facade exports through each runtime family; canonical `std.nogc_sync_mut.spec` tests own behavior |
| SPipe advanced condition package | `std.nogc_async_mut.spec.*`, `std.gc_async_mut.spec.*` | `bin/simple check src/lib/nogc_async_mut/spec/*.spl src/lib/gc_async_mut/spec/*.spl` validates the skip/ignore condition package parses through each runtime family; files are mechanical copies of the canonical no-GC sync package |
| `src` top-level utility facades | `std.nogc_async_mut.src.*`, `std.gc_async_mut.src.*` | `test/unit/lib/*/src/src_time_facade_spec.spl` validates time read helpers through each runtime family; other top-level `src` utilities are mechanically re-exported and remain syntax/import covered alongside existing subpackage specs |
| `src.app` mapped-file facade | `std.nogc_async_mut.src.app.mapped_file`, `std.gc_async_mut.src.app.mapped_file` | `test/unit/lib/*/src/app/src_app_mapped_file_facade_spec.spl` validates mapped-file record helpers and bounds checks through each runtime family |
| TUI widget family facades | `std.nogc_async_mut.tui.widgets.*`, `std.gc_async_mut.tui.widgets.*` | `test/unit/lib/*/tui/widgets/tui_widgets_facade_spec.spl` validates text, box, list, and input widget behavior without launching a TUI; canonical widget substring calls are interpreter-safe |
| TUI core family facades | `std.nogc_async_mut.tui.{style,widget,layout,terminal}`, `std.gc_async_mut.tui.*` | `test/unit/lib/*/tui/tui_facade_spec.spl` validates style rendering, rect/render-buffer helpers, and layout splits through each runtime family; terminal raw-mode and screen I/O remain extern-backed and syntax/import covered, and canonical core imports now point at `nogc_sync_mut.tui.*` |
| Tmux family facades | `std.nogc_async_mut.tmux.mod`, `std.gc_async_mut.tmux.mod` | `test/unit/lib/*/tmux/tmux_facade_spec.spl` validates tmux record exports through each runtime family; shell-backed tmux operations remain syntax/import covered |
| Terminal credential family facades | `std.nogc_async_mut.terminal.credential.*`, `std.gc_async_mut.terminal.credential.*` | `test/unit/lib/*/terminal/credential/terminal_credential_facade_spec.spl` validates plaintext resolution and encrypted-prefix helpers through each runtime family; key-file generation, encryption, and config parsing remain hosted/syntax-checked |
| Text layout family facades | `std.nogc_async_mut.text_layout.*`, `std.gc_async_mut.text_layout.*` | `test/unit/lib/*/text_layout/text_layout_facade_spec.spl` validates default font metadata, vector glyph tables, font-face source helpers, and renderer/cache records through each runtime family; TTF rasterization and font materialization remain syntax/import covered |
| Test spec parity shims | `std.nogc_async_mut.test.{coverage_spec,mcdc_spec}`, `std.gc_async_mut.test.*` | `bin/simple check src/lib/*/test/{coverage_spec,mcdc_spec}.spl` validates the pending legacy spec modules parse through each runtime family; no runtime behavior is introduced |
| Testing attributes facades | `std.nogc_async_mut.testing.*`, `std.gc_async_mut.testing.*` | `test/unit/lib/*/testing/testing_attributes_facade_spec.spl` validates test metadata records and timeout/retry validators through each runtime family |
| Test runner family facades | `std.nogc_async_mut.test_runner.*`, `std.gc_async_mut.test_runner.*` | `test/unit/lib/*/test_runner/test_stats_facade_spec.spl` validates deterministic test statistics helpers through each runtime family; broader test-runner orchestration, process, QEMU, DB, and container paths are mechanically re-exported and remain syntax/import covered |
| Terminal top-level facades | `std.nogc_async_mut.terminal.*`, `std.gc_async_mut.terminal.*` | `test/unit/lib/*/terminal/terminal_types_facade_spec.spl` validates terminal and power type factories through each runtime family; SSH, telnet, T32, relay, and dispatch backends remain syntax/import covered |
| TCP tuple utility facades | `std.nogc_async_mut.tcp.*`, `std.gc_async_mut.tcp.*` | `test/unit/lib/*/tcp/tcp_facade_spec.spl` validates TCP connection tuple helpers, state predicates, formatting, and validators through each runtime family |
| TLS family facades | `std.nogc_async_mut.tls.*`, `std.gc_async_mut.tls.*` | `test/unit/lib/*/tls/tls_facade_spec.spl` validates record, handshake, alert, cipher, hex utility, and hostname helpers through each runtime family; certificate file I/O and X.509 parsing remain syntax/import covered |
| Timing utility facades | `std.nogc_async_mut.timing`, `std.gc_async_mut.timing` | `test/unit/lib/*/timing_facade_spec.spl` validates timing record exports through each runtime family; wall-clock/profile execution remains syntax/import covered |
| web_ui render bridge | `std.nogc_sync_mut.web_ui.bridge` hosted packed-pixel renderer | no examples/browser renderer dependency |
| web_ui DOM backend | `std.nogc_sync_mut.web_ui.dom_backend` local DOM store | no examples/browser DOM dependency |
| web_ui family facades | `std.nogc_async_mut.web_ui.*`, `std.gc_async_mut.web_ui.*` | `test/unit/lib/*/web_ui/web_ui_facade_spec.spl` validates payload maps, command registry basics, event/input/plugin/config helpers, pixel packing, and DOM attr records through each runtime family; SDL windowing, render bridge runtime presentation, app loop, and file I/O plugin paths remain syntax/import covered |
| WebSocket family facades | `std.nogc_async_mut.websocket.{types,handshake,frame,connection,message,utilities}`, `std.gc_async_mut.websocket.*` | `test/unit/lib/*/websocket/websocket_facade_spec.spl` validates protocol constants, upgrade string helpers, close-status helpers, and frame summary helpers through each runtime family; legacy byte/frame payload helpers remain syntax/import covered pending a dedicated array/list cleanup, and `std.nogc_async_mut.websocket.upgrade` remains an async-only extra |
| Web framework family facades | `std.nogc_async_mut.web_framework.*`, `std.gc_async_mut.web_framework.*` | `test/unit/lib/*/web_framework/web_framework_facade_spec.spl` validates asset URL helpers, CSRF HTML helpers, form header/content-type parsing, RBAC permission records, and trace ID formatting through each runtime family; database, Redis, JWT/HMAC, random/time, and filesystem-backed paths remain syntax/import covered, while `std.nogc_async_mut.web_framework.{app,dispatcher,live_reload,router}` remain async-only extras |
| Unsafe helper family facades | `std.nogc_async_mut.unsafe.*`, `std.gc_async_mut.unsafe.*` | `test/unit/lib/*/unsafe/unsafe_facade_spec.spl` validates struct layout metadata and typed `MaybeUninit` helpers through each runtime family; canonical `unsafe.mod` now re-exports from `nogc_sync_mut.unsafe.maybe_uninit` instead of the stale `std.unsafe` namespace |
| UI test client family facades | `std.nogc_async_mut.ui_test.*`, `std.gc_async_mut.ui_test.*` | `test/unit/lib/*/ui_test/ui_test_facade_spec.spl` validates UI element/state records and JSON field/object parsing through each runtime family; TCP HTTP client operations remain syntax/import covered, and canonical parser now reads `text_content` before falling back to legacy `text` |
| UI platform/access family facades | `std.nogc_async_mut.ui.{platform_material,access_store}`, `std.gc_async_mut.ui.{platform_material,access_store}` | `test/unit/lib/*/ui/ui_platform_facade_spec.spl` validates platform material CSS helpers through each runtime family; SQLite-backed access-store operations remain syntax/import covered, and `std.nogc_async_mut.ui.{async_loop,async_reactive,wine_x11_adapter}` remain async-only extras |
| UDP utility family facades | `std.nogc_async_mut.udp_utils`, `std.gc_async_mut.udp_utils` | `test/unit/lib/*/udp_utils_facade_spec.spl` validates socket state, datagram metadata, port/address classifiers, fragmentation helpers, and multicast/broadcast send checks through each runtime family |
| Browser transition computed style | `std.gc_async_mut.gpu.browser_engine.style.computed_style` | examples adapt richer browser styles to this contract |
| Binary I/O module parity | `std.nogc_async_mut.binary_io`, `std.gc_async_mut.binary_io` | `bin/simple check src/lib/nogc_async_mut/binary_io.spl src/lib/gc_async_mut/binary_io.spl` validates endian-aware binary reader/writer helpers parse through each runtime family |
| Atomic/array/AWS SigV4 module parity | `std.nogc_async_mut.{atomic,array,aws_sigv4}`, `std.gc_async_mut.{atomic,array,aws_sigv4}` | `bin/simple check src/lib/nogc_async_mut/aws_sigv4.spl src/lib/gc_async_mut/aws_sigv4.spl src/lib/nogc_async_mut/atomic.spl src/lib/gc_async_mut/atomic.spl src/lib/nogc_async_mut/array.spl src/lib/gc_async_mut/array.spl` validates runtime atomic wrappers, array helpers, and AWS SigV4 canonical signing helpers parse through each runtime family |
| Linear algebra/NDArray package roots | `std.nogc_async_mut.linalg`, `std.gc_async_mut.linalg`, `std.nogc_async_mut.ndarray`, `std.gc_async_mut.ndarray` | `bin/simple check src/lib/gc_async_mut/linalg/__init__.spl src/lib/gc_async_mut/ndarray/__init__.spl` validates the GC async package roots for linear algebra and NDArray now match the existing nogc async roots and parse cleanly |
| Allocator/advanced-array/AMQP utility parity | `std.nogc_async_mut.{allocator,array_advanced,amqp_utils}`, `std.gc_async_mut.{allocator,array_advanced,amqp_utils}` | `bin/simple check src/lib/nogc_async_mut/array_advanced.spl src/lib/gc_async_mut/array_advanced.spl src/lib/nogc_async_mut/amqp_utils.spl src/lib/gc_async_mut/amqp_utils.spl src/lib/nogc_async_mut/allocator.spl src/lib/gc_async_mut/allocator.spl` validates allocator helpers, advanced array helpers, and AMQP utility encoding helpers parse through each runtime family |
| Benchmark package parity | `std.nogc_async_mut.benchmark.*`, `std.gc_async_mut.benchmark.*` | `bin/simple check src/lib/nogc_async_mut/benchmark/*.spl src/lib/gc_async_mut/benchmark/*.spl` validates benchmark config, stats, compare, measure, report, string benchmark, type, utility, and root modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/benchmark` |
| Buffer package parity | `std.nogc_async_mut.buffer.*`, `std.gc_async_mut.buffer.*` | `bin/simple check src/lib/nogc_async_mut/buffer/*.spl src/lib/gc_async_mut/buffer/*.spl` validates create, read, seek, write, type, and utility modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/buffer` |
| Cache package parity | `std.nogc_async_mut.cache.*`, `std.gc_async_mut.cache.*` | `bin/simple check src/lib/nogc_async_mut/cache/*.spl src/lib/gc_async_mut/cache/*.spl` validates create, get, set, evict, type, utility, and root modules parse through each runtime family; exact package parity is maintained against `nogc_sync_mut/cache` |
| Null block reference driver | `std.driver.null_block_driver` | SimpleOS examples/tests no longer need to own registry contract coverage |
| Driver framework family facades | `std.nogc_async_mut.driver.*`, `std.gc_async_mut.driver.*` | `test/unit/lib/*/driver/driver_facade_spec.spl` validates driver types, errors, manifest ABI, and null-block operations through package imports; `bin/simple check src/lib/nogc_async_mut/driver/*.spl src/lib/gc_async_mut/driver/*.spl` also covers loader and native library modules with GPU driver imports rewritten to each owning family |
| Drawing package parity | `std.nogc_async_mut.drawing.*`, `std.gc_async_mut.drawing.*` | `bin/simple check src/lib/nogc_async_mut/drawing/*.spl src/lib/gc_async_mut/drawing/*.spl` validates brush, rasterizer, compositor, and drawing tool app modules parse through each runtime family; local drawing imports are rewritten to each owning family |
| Hook detector family facades | `std.nogc_async_mut.hooks.detectors.*`, `std.gc_async_mut.hooks.detectors.*` | `test/unit/lib/*/hooks/detectors/hooks_detectors_facade_spec.spl` validates build, feature, task, and TODO detector missing-file summaries plus priority mapping |
| Hooks package parity | `std.nogc_async_mut.hooks.*`, `std.gc_async_mut.hooks.*` | `bin/simple check src/lib/nogc_async_mut/hooks/*.spl src/lib/gc_async_mut/hooks/*.spl` validates hook registration/runtime and stop-hook entrypoints parse through each runtime family |
| Game2D backend family facades | `std.nogc_async_mut.game2d.backend.*`, `std.gc_async_mut.game2d.backend.*` | `test/unit/lib/*/game2d/backend/game2d_backend_facade_spec.spl` validates deterministic frame hashing, window/event records, headless backend construction, and SDL stub construction; canonical backend constructors use `InputSnapshot.create()` |
| Game2D asset family facades | `std.nogc_async_mut.game2d.asset.*`, `std.gc_async_mut.game2d.asset.*` | `test/unit/lib/*/game2d/asset/game2d_asset_facade_spec.spl` validates typed asset IDs, asset diagnostics, atlas construction, and empty table state; full loader/table wrappers are syntax-checked |
| Game2D audio family facades | `std.nogc_async_mut.game2d.audio.*`, `std.gc_async_mut.game2d.audio.*` | `test/unit/lib/*/game2d/audio/game2d_audio_facade_spec.spl` validates sound metadata constructors, volume derivation, backend-missing diagnostics, and stub playback result through each runtime family; canonical audio init now exports `Sound` explicitly |
| Game2D input family facades | `std.nogc_async_mut.game2d.input.*`, `std.gc_async_mut.game2d.input.*` | `test/unit/lib/*/game2d/input/game2d_input_facade_spec.spl` validates key/button constructors, deterministic snapshots, and current-frame input accessors through each runtime family; exact subtree parity is maintained against `nogc_sync_mut/game2d/input` |
| Game2D package root parity | `std.nogc_async_mut.game2d`, `std.gc_async_mut.game2d` | `bin/simple check src/lib/nogc_async_mut/game2d/__init__.spl src/lib/gc_async_mut/game2d/__init__.spl` validates the Game2D package root parses through each runtime family; package imports are rewritten to each owning family |
| Game2D math package parity | `std.nogc_async_mut.game2d.math`, `std.gc_async_mut.game2d.math` | `bin/simple check src/lib/nogc_async_mut/game2d/math/__init__.spl src/lib/gc_async_mut/game2d/math/__init__.spl` validates the Game2D math package root parses through each runtime family |
| Game2D app family facades | `std.nogc_async_mut.game2d.app.*`, `std.gc_async_mut.game2d.app.*` | `test/unit/lib/*/game2d/app/game2d_app_facade_spec.spl` validates app defaults and game/window/runtime config records through each runtime family; hosted `run` wrappers are syntax-checked |
| Game2D config family facades | `std.nogc_async_mut.game2d.config.*`, `std.gc_async_mut.game2d.config.*` | `test/unit/lib/*/game2d/config/game2d_config_facade_spec.spl` validates window, runtime, and game configuration defaults through each runtime family; file-backed SDN loading remains extern-backed and syntax/import covered |
| Game2D render family facades | `std.nogc_async_mut.game2d.render.*`, `std.gc_async_mut.game2d.render.*` | `test/unit/lib/*/game2d/render/game2d_render_facade_spec.spl` validates image diagnostics and font metric constants through each runtime family; `Canvas` and `Font` wrappers are syntax-checked because canonical `Font` construction has a runtime name-collision edge |
| Game2D time family facades | `std.nogc_async_mut.game2d.time.*`, `std.gc_async_mut.game2d.time.*` | `test/unit/lib/*/game2d/time/game2d_time_facade_spec.spl` validates deterministic callback time, seeded random reproducibility, random aliases, and time-state construction through each runtime family; non-deterministic wall-clock reads remain extern-backed |
| Game2D loop family facades | `std.nogc_async_mut.game2d.loop.*`, `std.gc_async_mut.game2d.loop.*` | `test/unit/lib/*/game2d/loop/game2d_loop_facade_spec.spl` validates fixed-step accumulator construction and consumption through each runtime family; canonical loop driver mutation methods now use mutable receivers |
| mcpgdb protocol schema | `app.mcpgdb.protocol` | `examples.mcpgdb.protocol` re-exports |
| Host taskbar demo manifest/content | `app.ui.web.taskbar_demo_app` | `examples.hello_taskbar.*` re-exports |

Current enforced guard:

- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `os.*` imports from `src/lib`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct POSIX or
  Linux namespace imports from `src/lib`, including `posix.*`, `linux.*`,
  `std.posix.*`, `std.linux.*`, and `os.posix.*`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `examples.*` imports from `src/lib`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct imports from
  `src/lib/nogc_async_mut_noalloc` into allocating runtime families
  (`std.nogc_sync_mut.*`, `std.nogc_async_mut.*`,
  `std.nogc_async_immut.*`, `std.gc_async_mut.*`).
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `app.*`
  imports from `src/lib/nogc_async_mut_noalloc`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new `@alloc` module
  annotations in `src/lib/nogc_async_mut_noalloc`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `examples.*`
  imports from library tests under `test/unit/lib` and `test/feature/lib`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `examples.*`
  imports from any non-generated test source under `test/`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `examples.*`
  imports from production app code under `src/app`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new direct `examples.*`
  imports from production system specs under `doc/06_spec` (generated
  `.spipe_matchers_*` files are excluded from this guard).
- The import guard covers eager and lazy forms such as `use examples.*` and
  `use lazy examples.*`.
- `test/unit/lib/dependency_boundary_spec.spl` fails if production code or
  library tests import `common.pure.runtime`; hosted callers should use concrete
  no-GC backend surfaces such as `std.io.time_now_unix_micros`.
- `test/unit/lib/dependency_boundary_spec.spl` fails on new host-platform markers
  (`/proc`, `/sys`, `fork`, `ptrace`, `epoll`, process shell-outs, and direct
  POSIX-style directory/stat externs) outside approved backend or documented
  contract paths.
- No direct `os.*` imports are allowed from `src/lib`.
- No direct `examples.*` imports are allowed from `src/lib`.

Remaining coupling inventory:

- Direct `src/lib` imports from `os.*` and `examples.*` are now closed by test.
- Direct `src/app` and `doc/06_spec` imports from `examples.*` are now closed
  by test for non-generated Simple sources.
- Direct noalloc imports from allocating runtime families, direct `app.*`
  imports, explicit noalloc `@alloc` markers, and host allocation API calls are
  now closed by test and the baremetal verifier; noalloc QEMU execution keeps
  local adapter/debug contracts rather than importing the hosted DAP or app
  debug stacks.
- POSIX/Linux-hosted implementation hooks are intentionally backend-local in
  `nogc_sync_mut/`, `nogc_async_mut/`, `nogc_async_mut_noalloc/`,
  `gc_async_mut/`, `hardware/`, and `ffi/`. The root `process_monitor.spl` is a
  compatibility shim to the `nogc_sync_mut` backend.
- `common/wine_*` remains an explicit contract/modeling surface. It names POSIX,
  pthread, and host features but does not import OS modules directly.
- Historical host behavior in `common/js/node/*`, `common/mathjax.spl`,
  `common/pure/runtime.spl`, and `common/chaos.spl` now has deterministic
  no-host fallbacks. Active production imports of `common.pure.runtime` are
  blocked. Future work should move any real executable host adapters into a
  concrete runtime family or keep only pure contracts in `common/`.
- Remaining direction work: retire or relocate the frozen common host
  exceptions, move any remaining example-only tests that cover production
  contracts to stdlib-owned fixtures, and continue GC/NoGC/async parity
  completion.
- Direct `examples.*` imports from non-generated test sources are removed and
  covered by the boundary regression test. The POSIX remount namespace, POSIX
  raw/NVMe mirror, DBFS in-memory arena, NVFS raw/NVMe arena, superblock disk,
  and storage-constant contracts now have stdlib-owned fixture surfaces.

Rejected split:

- Replacing `BaremetalBackend.fb: FramebufferDriver` with `fb: any` removed the
  static import but caused `Engine2D.create_with_baremetal_backend*()` to retain
  a CPU backend instead of a baremetal backend in
  `test/unit/lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl`.
  The accepted split is a typed library-owned framebuffer surface contract, with
  the OS driver implementing/adapting that contract, not dynamic `any`.

Follow-up required before claiming full completion:

- Audit POSIX/Linux-specific hosted FFI assumptions in `src/lib`.
- Decide which example-only NVFS arena tests should move to stdlib contract
  tests.
- Add broader production import gates only after remaining ownership boundaries
  outside `src/lib`, `src/os`, and `src/app` are intentionally normalized.

---

## Module Parity Table

| Module | `gc_async_mut/` | `nogc_sync_mut/` | `nogc_async_mut/` | `common/` shared types |
|--------|:--------------:|:----------------:|:-----------------:|:----------------------:|
| `torch` | ✅ | ✅ | ✅ | `common/torch/interface.spl` — `TorchBackend`, `LayerForward`, `HasParameters` |
| `cuda` | ✅ | ✅ | ✅ | — |
| `gpu` | ✅ | ✅ | ✅ | `common/gpu/device.spl` — `GpuBackend`, `Gpu`, constructors |
| `gpu_runtime` | ✅ | ✅ | ✅ | — |
| `pure` (ML algorithms) | ✅ | ✅ | ✅ | — (tensor, autograd, nn, training, data — no FFI handles) |
| `torch/dyn_ffi` | ✅ | ✅ | ✅ | — (identical, stateless DynLoader wrappers) |
| `gpu_driver` | ✅ (`gpu.spl`, `gpu_driver/`) | ✅ (`gpu_driver/`) | ✅ (`gpu_driver/`) | — (local extern fn replaces import) |
| `ml` (async-specific) | — | — | ✅ | — (async training loops + data pipeline utils) |
| math blocks `m{}` | ✅ | ✅ | ✅ | — (language feature, available in all modes) |

### Modules with NoGC copies (originals retained in `gc_async_mut/`)

| Module | NoGC Copy | Notes |
|--------|-----------|-------|
| `torch/dyn_ffi.spl` | `nogc_sync_mut/torch/dyn_ffi.spl` | Stateless DynLoader wrappers — identical copy (2026-02-22) |
| `gpu.spl` (root) | `nogc_sync_mut/gpu_driver/` | Explicit lifecycle, no owns_handle — local `extern fn` replaces import (2026-02-22) |

**Note:** Source files remain in `gc_async_mut/` for GC-mode users. No modules pending migration.

### Modules only in `nogc_sync_mut/` (NoGC-first)

No modules currently remain in this list for the GPU migration surface.

---

## Common/ Extractions

### `common/torch/` (existing)

**File:** `src/lib/common/torch/interface.spl`

**Contents:**
- `TorchBackend` trait — handle-level ops (available, create_zeros, tensor_add, etc.)
- `LayerForward` trait — `fn forward(input: i64) -> i64`
- `HasParameters` trait — `fn parameter_handles() -> [i64]`

**Used by:**
- `gc_async_mut/torch/backend.spl` — `impl TorchBackend for GcTorchOps`
- `nogc_sync_mut/torch/backend.spl` — `impl TorchBackend for NogcTorchOps`

### `common/gpu/` (new, 2026-02-22)

**File:** `src/lib/common/gpu/device.spl`

**Contents:**
- `GpuBackend` enum — `Cuda`, `Vulkan`, `None_`
- `Gpu` struct — `backend: GpuBackend`, `device_id: i32`, `is_initialized: bool`
- `impl Gpu` — `is_valid() -> bool`, `sync() -> bool`
- `gpu_cuda(device_id: i32) -> Gpu`
- `gpu_vulkan(device_id: i32) -> Gpu`
- `gpu_none() -> Gpu`

**Used by:**
- `gc_async_mut/gpu/device.spl` — was the original definition
- `nogc_sync_mut/gpu/device.spl` — imports and re-exports

---

## Import Mapping

When migrating user code from GC to NoGC, apply these import substitutions:

| GC Import | NoGC Import |
|-----------|-------------|
| `use std.torch.*` | `use std.nogc_sync_mut.torch.*` |
| `use std.gc_async_mut.torch.*` | `use std.nogc_sync_mut.torch.*` |
| `use std.cuda.*` | `use std.nogc_sync_mut.cuda.*` |
| `use std.gc_async_mut.cuda.*` | `use std.nogc_sync_mut.cuda.*` |
| `use std.gpu.*` | `use std.nogc_sync_mut.gpu.*` |
| `use std.gc_async_mut.gpu.*` | `use std.nogc_sync_mut.gpu.*` |
| `use std.gpu_runtime.*` | `use std.nogc_sync_mut.gpu_runtime.*` |
| `use std.gc_async_mut.gpu_runtime.*` | `use std.nogc_sync_mut.gpu_runtime.*` |
| `use std.gc_async_mut.pure.*` | `use std.nogc_sync_mut.pure.*` |
| `use std.gc_async_mut.torch.dyn_ffi.*` | `use std.nogc_sync_mut.torch.dyn_ffi.*` |
| `use std.gc_async_mut.gpu.*` | `use std.nogc_sync_mut.gpu_driver.*` |
| `use std.nogc_sync_mut.torch.*` | `use std.nogc_async_mut.torch.*` |
| `use std.nogc_sync_mut.cuda.*` | `use std.nogc_async_mut.cuda.*` |
| `use std.nogc_sync_mut.gpu.*` | `use std.nogc_async_mut.gpu.*` |
| `use std.nogc_sync_mut.pure.*` | `use std.nogc_async_mut.pure.*` |
| `use std.fs_driver.nvfs_arena.*` | `use std.nogc_async_mut.fs_driver.nvfs_arena.*` or `use std.gc_async_mut.fs_driver.nvfs_arena.*` |
| `use std.fs_driver.nvfs_superblock.*` | `use std.nogc_async_mut.fs_driver.nvfs_superblock.*` or `use std.gc_async_mut.fs_driver.nvfs_superblock.*` |
| `use std.storage.nvfs_constants.*` | `use std.nogc_async_mut.storage.nvfs_constants.*` or `use std.gc_async_mut.storage.nvfs_constants.*` |
| `use std.storage.storage_class.*` | `use std.nogc_async_mut.storage.storage_class.*` or `use std.gc_async_mut.storage.storage_class.*` |
| `use std.storage.durability.*` | `use std.nogc_async_mut.storage.durability.*` or `use std.gc_async_mut.storage.durability.*` |
| `use std.storage.nvme_feature_policy.*` | `use std.nogc_async_mut.storage.nvme_feature_policy.*` or `use std.gc_async_mut.storage.nvme_feature_policy.*` |
| `use std.db.dbfs_engine.arena.*` | `use std.nogc_async_mut.db.dbfs_engine.arena.*` or `use std.gc_async_mut.db.dbfs_engine.arena.*` |
| `use std.db.dbfs_engine.{txn,inline_data,wal}.*` | `use std.nogc_async_mut.db.dbfs_engine.{txn,inline_data,wal}.*` or `use std.gc_async_mut.db.dbfs_engine.{txn,inline_data,wal}.*` |
| `use std.db.dbfs_engine.{schema,file_meta}.*` | `use std.nogc_async_mut.db.dbfs_engine.{schema,file_meta}.*` or `use std.gc_async_mut.db.dbfs_engine.{schema,file_meta}.*` |
| `use std.db.dbfs_engine.{pager,checkpoint_ring,checkpoint,attr_index}.*` | `use std.nogc_async_mut.db.dbfs_engine.{pager,checkpoint_ring,checkpoint,attr_index}.*` or `use std.gc_async_mut.db.dbfs_engine.{pager,checkpoint_ring,checkpoint,attr_index}.*` |
| `use std.db.dbfs_engine.ns_btree.{DentryKey,Ino,NsBTree}` | `use std.nogc_async_mut.db.dbfs_engine.{NsDentryKey,NsIno,NsBTree}` or `use std.gc_async_mut.db.dbfs_engine.{NsDentryKey,NsIno,NsBTree}` |
| `use std.db.dbfs_engine.{intent_log,recovery}.*` | `use std.nogc_async_mut.db.dbfs_engine.{intent_log,recovery}.*` or `use std.gc_async_mut.db.dbfs_engine.{intent_log,recovery}.*` |
| `use std.db.dbfs_engine.{raw_nvme_arena,superblock}.*` | `use std.nogc_async_mut.db.dbfs_engine.{raw_nvme_arena,superblock}.*` or `use std.gc_async_mut.db.dbfs_engine.{raw_nvme_arena,superblock}.*` |
| `use std.db.dbfs_engine.fs_driver.DbfsFsDriver` | `use std.nogc_async_mut.db.dbfs_engine.fs_driver.DbfsFsDriver` or `use std.gc_async_mut.db.dbfs_engine.fs_driver.DbfsFsDriver` |
| `use std.db.dbfs_engine.meta_store.MetaStore` | `use std.nogc_async_mut.db.dbfs_engine.meta_store.MetaStore` or `use std.gc_async_mut.db.dbfs_engine.meta_store.MetaStore` |
| `use std.db.dbfs_driver.dbfs_driver.*` | `use std.nogc_async_mut.db.dbfs_driver.dbfs_driver.*` or `use std.gc_async_mut.db.dbfs_driver.dbfs_driver.*` |
| `use std.db.accel.*` | `use std.nogc_async_mut.db.accel.*` or `use std.gc_async_mut.db.accel.*` |
| `use std.db.*` | `use std.nogc_async_mut.db.*` or `use std.gc_async_mut.db.*` |
| `use std.database.sql.*` | `use std.nogc_async_mut.database.sql.*` or `use std.gc_async_mut.database.sql.*` |
| `use std.database.test_extended.*` | `use std.nogc_async_mut.database.test_extended.*` or `use std.gc_async_mut.database.test_extended.*` |
| `use std.nogc_sync_mut.compression.*` | `use std.nogc_async_mut.compression.*` or `use std.gc_async_mut.compression.*` |
| `use std.mcp_sdk.core.*` | `use std.nogc_async_mut.mcp_sdk.core.*` or `use std.gc_async_mut.mcp_sdk.core.*` |
| `use std.nogc_sync_mut.replay.{backend,event_log,trace_format,integration}.*` | `use std.nogc_async_mut.replay.{backend,event_log,trace_format,integration}.*` or `use std.gc_async_mut.replay.{backend,event_log,trace_format,integration}.*` |
| `use std.nogc_async_mut.replay.qemu_replay.*` | `use std.gc_async_mut.replay.qemu_replay.*` when GC/async consumers need the async-backed QEMU helpers |
| `use std.nogc_sync_mut.replay.core.*` | `use std.nogc_async_mut.replay.core.*` or `use std.gc_async_mut.replay.core.*` |
| `use std.nogc_sync_mut.replay.vm.*` | `use std.nogc_async_mut.replay.vm.*` or `use std.gc_async_mut.replay.vm.*` |
| `use std.nogc_sync_mut.replay.adapters.*` | `use std.nogc_async_mut.replay.adapters.*` or `use std.gc_async_mut.replay.adapters.*` |
| `use std.nogc_sync_mut.replay.process.*` | `use std.nogc_async_mut.replay.process.*` or `use std.gc_async_mut.replay.process.*` |
| `use std.nogc_sync_mut.replay.semantic.*` | `use std.nogc_async_mut.replay.semantic.*` or `use std.gc_async_mut.replay.semantic.*` |
| `use std.nogc_sync_mut.replay.container.*` | `use std.nogc_async_mut.replay.container.*` or `use std.gc_async_mut.replay.container.*` |

**Shared types** (no import change needed):
```simple
use std.common.gpu.device.{GpuBackend, Gpu}   # same in both modes
use std.common.torch.interface.{TorchBackend}  # same in both modes
```

---

## Pattern Differences by Module

### `cuda/` migration

| Aspect | GC (`gc_async_mut`) | NoGC (`nogc_sync_mut`) |
|--------|---------------------|------------------------|
| Class fields | `handle: i64`, `owns_handle: bool` | `handle: i64` only |
| Constructor | `CudaStreamWrapper(handle: h, owns_handle: true)` | `CudaStreamWrapper(handle: h)` |
| `drop()` | `if self.owns_handle: rt_cuda_stream_destroy(self.handle)` | `rt_cuda_stream_destroy(self.handle)` |
| API surface | Identical | Identical |

### `gpu/` migration

| Aspect | GC (`gc_async_mut`) | NoGC (`nogc_sync_mut`) |
|--------|---------------------|------------------------|
| Tensor type | `TorchTensorWrapper?` from `std.torch` | `Tensor?` from `std.nogc_sync_mut.torch` |
| Stream type | `TorchStream?` from `std.torch` | `Stream?` from `std.nogc_sync_mut.torch` |
| Device types | `GpuBackend`, `Gpu` defined in `gpu/device.spl` | Imported from `std.common.gpu.device` |
| Backend detection | `use std.torch.{torch_cuda_available}` | `use std.nogc_sync_mut.torch.{cuda_available}` |

### `gpu_runtime/` migration

The key difference is elimination of the borrowed-view pattern:

```simple
# GC: creates temporary wrapper with owns_handle: false
fn gpu_tensor_is_cuda(tensor_handle: i64) -> bool:
    val t = TorchTensorWrapper(handle: tensor_handle, owns_handle: false)
    t.is_cuda()

# NoGC: direct FFI call
fn gpu_tensor_is_cuda(tensor_handle: i64) -> bool:
    rt_torch_torchtensor_is_cuda(tensor_handle)
```

All 5 functions that used the borrowed-view pattern were replaced:
- `gpu_tensor_to_cuda` — `TorchTensorWrapper.cuda()` → `rt_torch_torchtensor_cuda()`
- `gpu_tensor_is_cuda` — `TorchTensorWrapper.is_cuda()` → `rt_torch_torchtensor_is_cuda()`
- `gpu_tensor_numel` — `TorchTensorWrapper.numel()` → `rt_torch_torchtensor_numel()`
- `gpu_stream_sync` — `TorchStream.sync()` → `rt_torch_torchstream_sync()`
- `gpu_stream_query` — `TorchStream.query()` → `rt_torch_torchstream_query()`

### `pure/` migration

Pure module contains only math/ML algorithms with no FFI handles:
- No `owns_handle` fields (pure value types)
- No `drop()` methods (no resources to free)
- Migration = bulk copy + fix 6 internal cross-references

| File | Old import | New import |
|------|-----------|------------|
| `nn.spl` | `std.gc_async_mut.pure.nn_layers` | `std.nogc_sync_mut.pure.nn_layers` |
| `evaluator.spl` | `std.gc_async_mut.pure.evaluator_broadcast` | `std.nogc_sync_mut.pure.evaluator_broadcast` |
| `parser.spl` | `std.gc_async_mut.pure.parser_expr` | `std.nogc_sync_mut.pure.parser_expr` |
| `evaluator_broadcast.spl` | `std.gc_async_mut.pure.evaluator` | `std.nogc_sync_mut.pure.evaluator` |
| `nn_layers.spl` | `std.gc_async_mut.pure.nn` | `std.nogc_sync_mut.pure.nn` |
| `parser_expr.spl` | `std.gc_async_mut.pure.parser` | `std.nogc_sync_mut.pure.parser` |

---

### nogc_async_mut ML Modules (new, 2026-02-22)

`nogc_async_mut/` now contains full copies of the ML library:

| Subsystem | Files | Source |
|-----------|------:|--------|
| `pure/` | 50 | Copy from `nogc_sync_mut/pure/` with import path fix |
| `torch/` | 8 | Copy from `nogc_sync_mut/torch/` with import path fix |
| `gpu/` | 5 | Copy from `nogc_sync_mut/gpu/` with import path fix |
| `cuda/` | 3 | Copy from `nogc_sync_mut/cuda/` with import path fix |
| `ml/` | 4 | New async-specific training integration |

The `ml/` module is unique to `nogc_async_mut/` and provides:
- `async_training.spl` — `train_epoch()`, `evaluate_model()`, `train_loop()`
- `data_pipeline.spl` — `prefetch_batches()`, `shuffle_indices()`

---

## Math Block m{} for ML

`m{}` is a language-level feature — available in **all** library modes (`gc_async_mut`, `nogc_sync_mut`, `nogc_async_mut`). No import required.

```simple
# Power operator inside m{} uses ^ (outside uses **)
val loss = m{ 0.5 * (pred - target)^2 }

# Broadcast operators for vectorized math
val scaled = m{ weights .* inputs }    # element-wise multiply
val dot    = m{ a @ b }               # matrix multiply
val t      = m{ matrix' }             # transpose

# Implicit multiplication
val norm = m{ 2*x^2 + 3x + 1 }       # 3x is 3 * x
```

All `m{}` expressions produce normal values — they compose with any ML code in any library mode.

---

## Async Module Parity

### Async modules in `nogc_async_mut/` (53 files, 9,795 lines)

The entire async library lives exclusively in `nogc_async_mut/`. There are **no** async modules in `gc_async_mut/`.

| Subsystem | Files | Key Modules |
|-----------|------:|-------------|
| Core async | 10 | `async/future.spl`, `async/promise.spl`, `async/executor.spl` |
| Host runtime | 10 | `async_host/scheduler.spl`, `async_host/runtime.spl`, `async_host/joinset.spl` |
| Actors | 2 | `actors/actor.spl` (588 lines) |
| Concurrent | 7 | `concurrent/channel.spl`, `concurrent/mutex.spl`, `concurrent/collections.spl` |
| I/O | 5 | `io/event_loop.spl`, `io/tcp.spl`, `io/file.spl` |
| Root | 19 | `actor_scheduler.spl`, `actor_heap.spl`, `supervisor.spl`, `gen_server.spl`, etc. |

### gc_async_mut async status

Despite the name, `gc_async_mut/` contains **only sync code**:
- `torch/` — synchronous tensor operations and training
- `cuda/` — synchronous CUDA stream/event/memory wrappers
- `gpu/` — synchronous GPU memory management
- `gpu_runtime/` — synchronous GPU runtime utilities
- `pure/` — synchronous math/ML algorithms

CUDA streams provide hardware-level async parallelism, but all Simple wrappers are synchronous function calls.

### Future GC async modules

When GC-aware async modules are created, they should follow these patterns:
- **Per-task heap:** Each async task gets its own GC heap (`ActorHeap` with GC presets)
- **Copy-on-send:** Cross-task messaging copies data (no shared references)
- **Arena fallback:** Short-lived tasks use `HeapConfig__no_gc(size)` for zero-GC overhead

### Async import mapping (future)

When GC async modules are created:

| GC Async Import | NoGC Async Import |
|-----------------|-------------------|
| `use std.gc_async.future.*` | `use std.async.*` |
| `use std.gc_async.actor.*` | `use std.actors.*` |
| `use std.gc_async.channel.*` | `use std.concurrent.channel.*` |

---

## Cross-References

- **Async migration guide:** [`doc/05_design/async_migration_guide.md`](async_migration_guide.md) — GC↔NoGC patterns for async code
- **nogc_async_mut architecture:** [`doc/07_guide/sync_async/async/nogc_async_mut_architecture.md`](../guide/sync_async/async/nogc_async_mut_architecture.md) — 53-file, 9,795-line async library
- **Cross-language async patterns:** [`doc/01_research/async_patterns_cross_language.md`](../research/async_patterns_cross_language.md) — Rust/Go/Erlang/Swift/Kotlin/Zig/C++/Python

---

## Verification Commands

```bash
# No owns_handle in any nogc module
grep -r 'owns_handle' src/lib/nogc_sync_mut/cuda/
grep -r 'owns_handle' src/lib/nogc_sync_mut/gpu/
grep -r 'owns_handle' src/lib/nogc_sync_mut/torch/dyn_ffi.spl  # 0 matches
grep -r 'owns_handle' src/lib/nogc_sync_mut/gpu_driver/         # 0 matches

# No gc_async_mut cross-references in nogc modules
grep -r 'gc_async_mut' src/lib/nogc_sync_mut/pure/

# File counts
find src/lib/nogc_sync_mut/cuda/ -name '*.spl' | wc -l         # 3
find src/lib/nogc_sync_mut/gpu/ -name '*.spl' | wc -l           # 5
find src/lib/nogc_sync_mut/gpu_runtime/ -name '*.spl' | wc -l   # 2
find src/lib/nogc_sync_mut/pure/ -name '*.spl' | wc -l          # 50
find src/lib/nogc_sync_mut/torch/ -name '*.spl' | wc -l         # 8 (was 7, +dyn_ffi.spl)
find src/lib/nogc_sync_mut/gpu_driver/ -name '*.spl' | wc -l    # 2
find src/lib/common/gpu/ -name '*.spl' | wc -l                  # 2

# nogc_async_mut file counts
find src/lib/nogc_async_mut/pure/ -name '*.spl' | wc -l     # 50
find src/lib/nogc_async_mut/torch/ -name '*.spl' | wc -l    # 8
find src/lib/nogc_async_mut/gpu/ -name '*.spl' | wc -l      # 5
find src/lib/nogc_async_mut/cuda/ -name '*.spl' | wc -l     # 3
find src/lib/nogc_async_mut/ml/ -name '*.spl' | wc -l       # 4

# GC pattern SPipe tests
find test/unit/lib/gc_async_mut/ -name 'gc_*_spec.spl' | wc -l  # 6
```
