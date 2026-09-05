# Pending Features

**Generated:** 2026-06-04
**Total Pending:** 116 features

## Summary

| Status | Count | Priority |
|--------|-------|---------|
| Failed | 0 | 🔴 Critical |
| In Progress | 0 | 🟡 High |
| Planned | 116 | 🟢 Medium |
| Ignored | 0 | ⚪ Low |

**Completion:** 0.0% (0 complete / 116 total)

---

## 🟢 Planned Features (116)

Features specified but not yet implemented

### `app/editor`_+_`lib/editor` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| EDITOR_MARKDOWN_EDITING_SUBSYSTEM_2026_05_28 | Editor markdown-editing subsystem (for full TUI render) | ## Context The editor controllers and render panels were written against a markdown-editing subsystem that was never implemented. With the rich `EditorBuffer` API + LSP result panel/popups now in place (landed 2026-05-28), the TUI launches  | - |

### `app/editor`_+_`lib/editor`_+_seed_runtime/jit (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| EDITOR_TUI_RENDER_COMPLETION_2026_05_29 | Editor TUI render completion + ctrl module consolidation | ## Context The editor-TUI render goal is partly landed. On `main` as of `knrqtpow`: the `_layout_find_group_index_local` SIGSEGV is fixed (`.id.value`→`.id`, was deref'ing an `i64` as a pointer), and the previously-undefined UI-state types | - |

### `simple_web_html_layout_renderer.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-WEBRENDER-001 | Generic-HTML layout render speed under the interpreter | The real layout renderer paints text glyph-by-glyph; a realistic full page (`examples/06_io/ui/sample_page.html`, ~4 KB) renders in ~2m37s under `SIMPLE_EXECUTION_MODE=interpret`. That is correct but far too slow for any interactive or test | - |

### `simple_web_html_layout_renderer.spl`_+_`browser_renderer.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-WEBRENDER-003 | Chrome-compatible text antialiasing / CSS coverage | The real layout renderer covers block flow, the CSS cascade for color / background / font-size / text-align / padding / margin, and word-wrapped text. It does not implement Chrome-compatible glyph antialiasing, LCD subpixel/gamma compositin | - |

### `src/compiler/70.backend/linker/lib_smf.spl`_+_codegen (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0004 | `.drv_manifest` SMF section + emission from `@driver` attribute | The runtime decoder already exists (`src/lib/nogc_sync_mut/driver/loader.spl::decode_manifest` reads the "DRVS"" magic + 64B header defined in `driver/manifest.spl`). The writer is missing: the compiler must emit an SMF section kind" | - |

### `src/compiler_rust/compiler/src/codegen/instr/core.rs`_+_hir (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0002 | Cranelift `>>` backend fix (disambiguation + signedness) | The `>>` operator is broken in the Rust bootstrap Cranelift backend (memory note `feedback_cranelift_shr_bug.md`). Root cause is two-part: 1. The HIR `BinOp` enum overloads `>>` as both `ShiftRight` and `Compose` (function composition — `sr | - |

### `src/compiler_rust/compiler/src/hir/lower/*`, (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0008 | Rust-seed bitfield HIR/MIR/sema codegen (blocker for FR-0003) | `src/compiler_rust/type/src/checker_check.rs`, `src/compiler_rust/compiler/src/interpreter_eval.rs`, `src/compiler_rust/parser/src/types_def/mod.rs` The Rust seed parses `bitfield Name(T): a:4; b:28` today but has no | - |

### `src/lib/nogc_async_mut/http_server/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0003 | Route HTTP static files through capability-driven sendfile | Use `IoDriver.net_capabilities()` to select the fastest safe static-file response path: `sendfile` or zero-copy where supported, async read plus send otherwise. The portable behavior must remain the default for QEMU and CI. | - |

### `src/lib/nogc_async_mut/io/`_and_runtime_backend_adapters (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0004 | Add packet I/O backend boundary for AF_XDP or DPDK | Define a packet I/O backend boundary that can drive RX/TX rings through AF_XDP or DPDK while preserving the portable socket backend. This should be capability-gated and excluded from default QEMU CI unless explicitly enabled. | - |

### `src/lib/nogc_async_mut/io/connection_pool.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0013 | Add TCP connection pool for HTTP keep-alive reuse | Provide a pure Simple connection pool keyed by host:port that tracks idle file descriptors with timestamps, enforces max-idle-per-host, and exposes acquire/release/evict-expired operations. Pool stats (acquired, released, evicted) must be i | - |

### `src/lib/nogc_async_mut/io/packet_ring.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0010 | Add bounded ring-buffer data structure for packet RX/TX paths | Provide a pure Simple power-of-two ring buffer with push/pop/peek and a batch-drain operation bounded by a per-quantum budget. The ring must make empty vs full unambiguous via the head==tail convention and expose a one-line CI-log summary. | - |

### `src/lib/nogc_async_mut/io/scatter_gather.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0011 | Add scatter-gather I/O list types | Provide `IoVec` (buffer_id, offset, len) and `ScatterGatherList` types mirroring POSIX iovec so that send/recv paths can describe discontiguous buffer regions without copying into a single allocation. Include a byte-boundary split helper fo | - |

### `src/lib/nogc_async_mut/io/socket_options.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0012 | Add async TCP socket option record types | Mirror and extend the sync Nagle/keepalive helpers from `nogc_sync_mut/tcp/socket.spl` into a comprehensive `TcpSocketOptions` record covering nodelay, cork, quickack, keepalive (idle/interval/count), SO_LINGER, and sndbuf/rcvbuf. Provide n | - |

### `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl`_+_`gpu_driver/driver_adapter.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0006 | Real `fs_driver` + `gpu_driver` adapter integration | FS adapter probe/attach path verified 2026-05-29. The Phase D adapters register the drivers but stub every op (`init → Ok(())`, `probe → Reject`, everything else either `Ok(())` or `NotSupported`). Replace these stubs with real | - |

### `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl`_+ (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0007 | Port `Fat32Core` + `BlockDevice` into `src/lib/nogc_sync_mut/fs_driver/` to unblock FS adapter forwarding | `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` + `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` `fat32_stub.spl` used to pull the real FAT32 driver via `use os.services.fat32.fat32.{Fat32Driver as Fat32Core, BlockDevice}`. | - |

### `src/os/drivers/framebuffer/`,_`src/os/drivers/virtio/virtio_gpu.spl`, (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0011 | VGA/BGA framebuffer and VirtIO-GPU DMA acceleration boundary | compositor/display services Separate legacy VGA/BGA framebuffer acceleration from VirtIO-GPU DMA acceleration. VGA/BGA should use write-combining framebuffer mapping, dirty rectangles, and bounded blits. VirtIO-GPU should use the shared DMA | - |

### `src/os/services/netstack/`_and_`src/os/posix/socket_compat.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0001 | Add connect completion and nonblocking socket semantics | `connect()` must not report a completed TCP connection until the 3-way handshake reaches `ESTABLISHED`. Blocking sockets should wait or sleep on a bounded completion path; nonblocking sockets should return an errno-style in-progress result  | - |

### `src/os/services/netstack/tcp_connection.spl` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0002 | Complete TCP data path wakeups and close/error semantics | Finish the pure Simple TCP data path so socket send/recv operations have observable readiness, bounded buffering, peer close handling, RST propagation, and retransmission/timeout errors suitable for HTTP workloads. | - |

### `src/os/userlib/device.spl`,_`src/os/kernel/ipc/syscall.spl`, (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0009 | Shared DMA descriptor contract for net, file, and display drivers | driver framework capability surfaces Define one shared DMA descriptor contract for all high-throughput drivers: network RX/TX rings, storage direct I/O, and display/GPU transfer buffers. The descriptor must carry CPU virtual address, device | - |

### `src/os/userlib/device.spl`,_network_drivers,_block_drivers,_and (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0008 | Share DMA buffer ownership with storage and display drivers | display/GPU drivers Promote the existing `SharedDmaBuffer` shape into a common driver contract so network, file/block, and display drivers can exchange caller-owned DMA buffers without copying through ordinary heap memory. The contract must | - |

### `src/runtime/startup/baremetal/<arch>/`_+_`src/hardware/<arch>/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0005 | Per-arch DMA cache-maintenance runtime (6 arches) | `src/lib/nogc_sync_mut/io/dma.spl` landed with arch-agnostic API and barrier-only interpreter fallbacks. Each supported arch needs a real runtime implementation of `rt_dma_alloc`, `rt_dma_free`, `rt_dma_virt_of`, `rt_dma_phys_of`, `rt_dma_s | - |

### `test/01_unit/lib/gc_async_mut/gpu/browser_engine/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-WEBRENDER-002 | Pixel-level test coverage for the generic layout path | The new generic-HTML branch (`simple_web_layout_render_html_pixels`) is only exercised indirectly. Add a focused spec that feeds generic document HTML (heading + paragraph + a colored block, none of the heuristic markers) and asserts: the p | - |

### async_http_server,_memory_registration,_and_network_backend_layer (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0006 | Prototype RDMA/exoskeleton transport for web serving | Add an opt-in RDMA transport experiment for controlled deployments where web responses can use registered memory, queue pairs, and completion queues outside the normal TCP socket path. The default Simple web server must remain TCP-compatibl | - |

### compiler (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-001 | Fix self-hosted binary missing CompileOptions field accessors | The self-hosted release binary (`bin/release/x86_64-unknown-linux-gnu/simple`) fails to resolve `CompileOptions.low_memory` and `CompileOptions.mode` at runtime, producing "Function 'CompileOptions.low_memory' not found"" and ""Function 'Comp" | - |

### compiler_(cranelift_jit_/_hir_lowering) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-012 | JIT-compile pure-Simple software rendering loops (unblock high-DPI 2D) | Pure-Simple per-pixel rasterizers (e.g. the SDF software renderer in `examples/06_io/ui/engine2d_shapes_gui.spl`) currently fall back to the tree-walk interpreter because JIT/HIR lowering bails with `Cannot infer type: TypedInteger(0, U32)` | - |

### compiler_+_`src/lib/common/ui/`_+_browser_renderer (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-007 | Add style{} and ui{} authoring surfaces | Add typed UI/style authoring surfaces for theme tokens, widget trees, layout, and CSS-like cascade/layout behavior without encoding those semantics as raw SDN. - [x] `style{}` can define typed tokens and component rules. | [spec](doc/02_requirements/feature/all_regions.md) |

### compiler_+_domain_library (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-008 | Add music{} authoring with MusicXML interchange | Add a `music{}` authoring surface for scores, staves, measures, voices, rhythm, pitch, articulations, and metadata, with MusicXML as the first interchange target and MEI/LilyPond/ABC adapters deferred until the core model is stable. | [spec](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-009 | Add bim{} and city{} standards bindings | Add BIM and city-scale authoring surfaces that bind authored objects to IFC, bSDD, gbXML, and CityGML identities/properties before attempting deep geometry or simulation semantics. | [spec](doc/02_requirements/feature/all_regions.md) |

### compiler_+_geometry/domain_library (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-010 | Add cad{} parametric authoring and STEP AP242 export | Add a `cad{}` authoring surface for parametric parts, assemblies, constraints, tolerances/PMI, and manufacturing metadata, with STEP AP242 as the industrial exchange target. | [spec](doc/02_requirements/feature/all_regions.md) |

### compiler_+_std_schema_tooling (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-006 | Implement schema{} contracts and compatibility checks | Implement `schema{}` as Simple's cross-domain contract language for validation, versioning, field IDs, defaults, units, identities, ranges, regex constraints, canonical serialization, and compatibility evolution. | [spec](doc/02_requirements/feature/all_regions.md) |

### compiler_loader_surfaces_in_`src/compiler/99.loader/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-011 | Share loader core logic only across proven safe seams | The compatibility loader in `src/compiler/99.loader/module_loader.spl` and the lifecycle-aware runtime loader in `src/compiler/99.loader/loader/module_loader.spl` should share core unload and reload bookkeeping only where the behavior is pr | - |

### compiler_—_`src/compiler/20.hir/hir_lowering/`_+_`src/compiler/80.driver/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-003 | Add 2-pass import resolver to self-hosted HIR lowering | The self-hosted HIR lowerer (`HirLowering`) must mirror the Rust seed's two-pass import loading pipeline from `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`: | - |

### compiler_—_`src/compiler/20.hir/hir_types.spl`_+_`src/compiler/20.hir/hir_lowering/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-004 | Module-scoped symbol tables for correct cross-module name isolation | The driver uses a single shared `HirLowering` instance with a flat global `SymbolTable` scope to lower all modules in sequence. When two modules export the same type name (e.g., `CompileOptions` in `driver_core_types.spl` and `backend_types | - |

### compiler_—_import_resolver_/_name-resolution_pass (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-002 | Fix self-hosted import resolver: same-named structs in different modules shadow each other | When two structs share the same short name but live in different fully-qualified module paths (e.g., `compiler.common.driver_core_types.CompileOptions` vs `compiler.backend.backend.backend_types.CompileOptions`), the self-hosted compiler's  | - |

### compiler_—_parser,_ast,_tree-sitter_outline,_hir_metadata (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-005 | Add raw top-level domain block carrier | Add contextual top-level raw capture for approved domain block names (`schema`, `style`, `ui`, `music`, `bim`, `cad`, `city`, `rtl`) without making those words hard reserved in normal identifier positions. The initial carrier preserves bloc | [spec](doc/02_requirements/feature/all_regions.md) |

### crypto_/_interpreter_perf (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-CRYPTO-0001 | RSA-2048 modexp completes within interpreter test budget | PSS bigint micro-optimization. Current `HEAD` already contains the prior safe hot-path speedups in `src/os/crypto/rsa_pss.spl` (`_pss_bi_normalize` avoids copying already-normalized limb lists, `_pss_bi_get_bit` uses the same direct limb-ma | - |

### driver_/_compiler_frontend_+_hir_lowering (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0001 | Compiler sugar for `@driver(...)` and `@native_lib(...)` attributes | Today every driver registers into the shared registry by calling `register_static_driver(manifest, ops)` from a hand-written registration fn. The design doc promises the one-liner syntax `@driver(class = DriverClass.Block, vendor = 0x8086,  | - |

### ecdsa (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| ECDSA_P384_P521_RUNTIME_PRIMITIVES_2026_05_02 | ECDSA-P-384 + ECDSA-P-521 primitives for TLS 1.3 | **Filed:** 2026-05-02 **Filed by:** W11-C (TLS 1.3 sigalg coverage track) **Modules:** - `src/lib/nogc_sync_mut/io/signature_ffi.spl` (FFI extern path) - `src/os/crypto/ecdh_p384.spl`, `ecdsa_p384.spl`, `ecdh_p521.spl`, `ecdsa_p521.spl` (pu | - |

### engine2d (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02 | Engine2D Facade Must Preserve Backend Pixel Mutations | Date: 2026-06-02 Status: open Area: Engine2D, render backends, web renderer parity ## Problem Backend-executed parity evidence found that direct concrete backends preserve drawn pixels, but the generic `Engine2D` facade path can lose pixel  | - |

### hkdf (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| HKDF_RFC5869_2026_05_01 | HKDF RFC 5869 Implementation | **Date:** 2026-05-01 **Requested by:** hkdf_rfc5869_spec agent **Status:** FIXED (2026-05-10) ## Summary Add HKDF (HMAC-based Key Derivation Function) as defined in RFC 5869 to `src/lib/common/crypto/`. ## Motivation | - |

### https (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| HTTPS_SERVER_INTERPRETER_EXTERNS_2026_05_28 | HTTPS Server — Pure Simple TLS Record-Layer | **Date**: 2026-05-28 **Updated**: 2026-05-30 **Status**: In Progress — TLS 1.2 server record-layer wired; ALPN/TLS 1.3 remain **Priority**: High — gates HTTPS benchmarking, HTTP/2 ALPN, HTTP/3 ## What Was Done (2026-05-29) The original "Blo" | - |

### kv260-simple-rv64-network (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-KV260-NET-0001 | Verify SimpleOS RV64 web and SSH on KV260 FPGA | refuses QEMU-only proof and fails when required PL UART, network transport, HTTP, or SSH artifacts are missing. Physical hardware capture remains open. Add a real network-dependent verification lane for the KV260 Simple RV64 FPGA target. Th | - |

### lexer_+_parser_+_hir_+_struct_layout (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0003 | Native bitfield syntax `struct Foo @packed { a: u16:4 }` | FR-DRIVER-0008 (blocker) landed 2026-04-22; Rust seed now has full `@packed struct { f: T:N }` pipeline: parser (`types_def/mod.rs:334-365`) → HIR routing (`type_registration.rs:112-113` → `register_packed_struct_as_bitfield`) → bitfield co | - |

### llm-backed_medical_qa_app/server_handoff (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPIPE-LLM-0003 | Add medical safety and deployment evidence | Require safety, license, and deployment evidence | - |

### lzma2 (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| LZMA2_FULL_LCLPPB_2026_05_01 | LZMA2 — Full LC/LP/PB Property Support | `LC=3, LP=0, PB=2` (props byte `0x5D`). Full lc/lp/pb support landed 2026-05-10 via the restored `std.common.compress.lzma2` hosted XZ bridge. See `src/lib/common/compress/lzma2.spl`. ## Context | - |

### network_tests,_qemu_scenarios,_and_smoke_scripts (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0007 | Add network performance and timeout verification harness | Create bounded network performance checks that measure connection setup, request latency, throughput, RSS, and timeout behavior for the portable stack and each accelerated backend. | - |

### nvfs (10)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-BENCH-ARENA-ITER-001 | Reduce nvfs_arena_throughput iter counts for interpreter budget | A1 scenario (outer=1000, inner=1000 appends × 8 words = ~8M word-push ops) exceeded the | - |
| FR-BENCH-BASELINE-001 | Run bench harness with real clock and record baseline numbers | After FR-BENCH-CLOCK-001 wired `rt_time_now_nanos()`, run all 5 bench scripts (`fs_driver_mount_table.spl`, `nvfs_arena_throughput.spl`, `simple_db_wal_append.spl`, `run_all.spl`, `test/05_perf/bench/lib/timing.spl`) with the bootstrap bina | - |
| FR-BENCH-CLOCK-001 | Add rt_time_now_ns() for hosted and baremetal targets | Bench harness in `test/05_perf/bench/lib/timing.spl` calls `extern fn rt_time_now_ns() -> i64` but the symbol was absent from both hosted and baremetal runtimes. Hosted: backed by `clock_gettime(CLOCK_MONOTONIC)`. | - |
| FR-BENCH-CLOCK-002 | Replace PIT-ch2 TSC calibration with HPET/PMTMR | Current TSC calibration in `src/os/kernel/arch/x86_64/timer.spl` uses PIT channel 2 for a ~10ms measurement window. Virtualised QEMU HPET is available via the ACPI HPET table (MMIO counter at 100 MHz-ish) and provides better | - |
| FR-N3-001 | Replace flat pmap sidecar with B-tree keyed by (arena_id, offset) | The flat `_pmap_sidecar: [PmapSidecarEntry]` in `fs_driver_impl.spl` performs O(n) linear scan on every read and write path.  Replace it with a B-tree keyed by `(arena_id, offset)` so that insert and lookup are O(log n).  The B-tree must su | - |
| FR-NVFS-N4a-001 | Scrub repair path: detect + repair from reflink peers | `scrub_all` previously only detected checksum mismatches and reported them. Add a repair path: when a bad block is found, scan all pmap sidecar entries for a peer whose stored checksum matches the bad entry's expected checksum and | - |
| FR-NVFS-N4b-001 | Proactive scrub scheduler + META_DURABLE replica repair | N4a repair falls back to Unrepairable when no reflink peer has a good copy. N4b should (a) add a background-task scheduler that runs `scrub_all` periodically (honouring `throttle_ms`), and (b) extend the repair path to | - |
| FR-NVFS-N5b-001 | B-tree rebalancing on delete (merge / rotate) | `pmap_btree_remove` in N5a performs leaf-only deletion without rebalancing. After many deletes the tree can become unbalanced (under-filled nodes). Implement standard B-tree merge and rotation on delete so the tree remains | - |
| FR-NVFS-N6b-001 | Raw send / encrypted replication stream (btrfs-send style) | Stream a sealed MODEL_IMMUTABLE arena between peers without decrypting the payload.  Ciphertext + key metadata travel over the wire as a self-describing byte stream (magic `NVSR`, 16-byte header, per-arena begin/extent/end records). | - |
| FR-STORAGE-0004 | MountTable.resolve() uses slice() which is broken in baremetal Cranelift | Rewrite `MountTable.resolve(path)` in `src/lib/nogc_sync_mut/fs_driver/mount_table.spl:129` so it does NOT call `path.raw.slice(mp_len, …)`. Cranelift's baremetal codegen has a known-broken `slice()` operation (per the hazard comment already in `shell_serial_entry.spl`); any baremetal caller routed through the mount ta | - |

### nvfs__(src/os/services/nvfs/src/core/arena.spl_or_new_constants.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPOSTGRE-M2-002 | Add named StorageClass and DurabilityClass constants to NVFS core | `src/os/services/nvfs/src/core/arena.spl` uses `class_tag: i32` as an opaque ordinal with no named constants. Consumers (Simple DB, future callers) must either duplicate ordinal assignments or rely on comments that say "matching nvfs i" | - |

### nvfs__(src/os/services/nvfs/src/core/compression.spl_—_new) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NVFS-N7a-001 | Inline compression: per-arena LZ4/Zstd, class-aware defaults | Add an inline compression layer (N7a) between the logical block and the physical device. Compression is per-dataset, per-arena, and opt-in via mount option `compress=<algo>` | - |

### nvfs__(src/os/services/nvfs/src/core/dedup.spl_—_new) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NVFS-N7b-001 | Inline deduplication: content-addressable DDT extending reflink machinery | Add an inline deduplication layer (N7b) backed by a content-addressable Deduplication Table (DDT). The DDT maps `content_hash (u8[32]) → DedupEntry` where DedupEntry carries the canonical logical_page_no, birth_gen, refcount, and flags (56  | - |

### nvfs__(src/os/services/nvfs/src/core/encryption.spl) (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NVFS-N6a-001 | Wire real AES-128-GCM into NVFS leaf DEK encrypt/decrypt | `encryption.spl` stubs (`_aes128_encrypt_stub` / `_aes128_decrypt_stub`) use XOR + checksum instead of real AES-128-GCM. Replace with calls to | - |
| FR-NVFS-N6a-002 | KDF hardening: salted derivation for per-arena dataset keys | `_derive_data_key_bytes` used a plain XOR of master_key bytes and arena_id with no domain separation or salt. Upgrade to a salted derivation that includes | - |

### nvfs__(src/os/services/nvfs/src/core/encryption.spl_+_arena.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NVFS-N6a-003 | DEK rotation on arena seal | On `arena_seal_impl`, if the arena is registered as encrypted in the `EncryptionInfo` registry, derive a fresh DEK (bumped generation) and update | - |

### nvme,_virtio-blk,_vfs/fs-driver_interface (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-DRIVER-0010 | DMA-backed file/block driver direct I/O path | Add a direct I/O path for file and block drivers where callers can pass a shared DMA buffer to read/write without copying through intermediate VFS heap buffers. Buffered file APIs remain the default; direct I/O must require an explicit flag | - |

### os-kernel_(src/os/kernel/ipc/spm_port.spl_+ (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPM-0003 | Rebind syscall for SPM port when real SPM task id is known | src/os/kernel/ipc/syscall.spl + src/os/kernel/types/syscall_types.spl) Kernel init now registers `SPM_WELL_KNOWN_TASK_ID = 0xfffffff0` via `spm_port_register` (see `init_services.spl::init_spm_port` and the `6353c53526` commit body). When t | - |

### os-kernel_(src/os/kernel/ipc/syscall.spl_+ (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPM-0002 | Caller-TaskId → privilege-mirror lookup for `sys_priv_check` (case 110) | src/os/kernel/privilege/privilege_bridge.spl) `_handle_spm_priv_check` in syscall.spl currently always returns `0` (deny) because it has no path from "the syscall that just arrived"" to `bridge_lookup(caller_task_id)`. Wire the caller's `Tas" | - |

### os-kernel_(src/os/kernel/ipc_+_src/os/kernel/memory) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPM-0001 | Page-table-walk read primitive for cross-page / non-identity-physmap user reads | Expose a `pt_walk(space: ProcessVmSpace, vaddr: u64) -> u64?` (or equivalent "translate user VA → kernel-readable pointer"") helper in `src/os/kernel/memory/vmm.spl`. Consumers: `_copy_in_bytes` (src/os/kernel/ipc/syscall.spl), `GrantTable.s" | - |

### os__(src/os/kernel/acpi/) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SIMPLEOS-ACPI-001 | ACPI table walker (RSDP → RSDT/XSDT → FADT + HPET) | SimpleOS needs real HPET MMIO base and PMTMR I/O port from ACPI tables so that TSC calibration can use sub-0.1% reference sources instead of PIT-ch2. | - |

### os__(src/os/services/vfs/vfs_init.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SIMPLEOS-M5-001 | VFS select-file cursor semantic (VfsCursor singleton) | `rt_fat32_select_file` (retired in M5) held a static 64-byte name cursor that callers used to remember the last-selected file before operating on it. | - |

### p256 (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| P256_SCALAR_MULT_CONSTANT_TIME_2026_05_01 | Constant-time P-256 scalar multiplication | **Filed:** 2026-05-01 **Module:** `src/os/crypto/ecdh_p256.spl` **Severity:** P0 before any caller exposes the ephemeral private key through the TLS 1.3 `handshake_secret` schedule. **Status: CLOSED 2026-05-01 — replaced naive double-and-ad | - |

### parser_/_`src/compiler/` (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-COMPILER-012-2 | FR-COMPILER-012 — Fix `expect (expr) == val` parser precedence | `expect (true and true) == true` is currently parsed as `(expect(true and true)) == true` — i.e., `expect` consumes the parenthesized sub-expression as its argument and the trailing `== true` is evaluated against the return value of `expect | - |

### plugin (3)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0002-2 | FR-PLUG-0002 (structural) — `.so` block-proxy constructor | Implemented in pure Simple. `_SoBlockProxy(BlockDefinition)` struct added to `src/compiler/15.blocks/plugin_startup.spl`. `activate_plugin` now dlsyms `<ClassName>_keyword` and `<ClassName>_parse` for each `block:` function entry, construct | - |
| FR-PLUG-0003-2 | FR-PLUG-0003 (structural) — Sugar registry AST round-trip | Implemented in pure Simple: - `DesugarRule` extended with `ast_rewrite_fn: i64` in `sugar_registry.spl` - `apply_rule_ast` and `apply_sugar_rules_ast` functions added to `sugar_registry.spl` - `desugar_collections` loop in `collection_desug | - |
| FR-PLUG-0004-2 | FR-PLUG-0004 (verification only) — Static lowering markers | Pure-Simple verification added to `test/03_system/feature/plugin/sugar_plugin_spec.spl` for the `[STATIC-NEXT]` handoff markers in the sugar registry, collection desugar loop, and backend matmul lowering site. Backend fusion remains open. # | - |

### plugin_/_15.blocks (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0002 | `.so` block-proxy constructor for `activate_plugin` | constructs+registers it for each `"block:""` manifest entry via `spl_dlsym` in `src/compiler/15.blocks/plugin_startup.spl` (see `activate_plugin` loop, FR-PLUG-0002 DONE comment). `TODO-FR-PLUG-0003-COMPATIBLE` at line 267 intentionally left" | - |

### plugin_/_15.blocks_/_10.frontend.desugar (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0003 | Sugar registry AST round-trip | `src/compiler/15.blocks/sugar_registry.spl`. `apply_rule_ast` and `apply_sugar_rules_ast` implemented and exported. `desugar_collections` loop in `src/compiler/10.frontend/desugar/collection_desugar.spl` carries `[FR-PLUG-0003 DONE]` commen | - |

### plugin_/_70.backend.cranelift (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0004 | Static lowering / fusion of sugar rules through Cranelift | AC-3 v1 ships a *dynamic-load* sugar registry consulted by the interpreter. The `[STATIC-NEXT]` marker at `c_backend_translate_ops.spl:145` (the Cranelift matmul emit site) is the insertion point for compile-time specialization: when a rule | - |

### plugin_/_compiler_/_di (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0005 | DI runtime-slot plugin loader integration | found in any `.spl` source. `src/compiler/00.common/di_runtime.spl` is a string-keyed lazy engine (`di_register`/`di_resolve`) — no slot syntax. `src/compiler/00.common/di_config.spl` parses `config/di.sdn` for `DiServiceConfig` entries but | - |

### plugin_/_runtime (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-PLUG-0001 | WFFI f64 calling-convention extern | Add `extern fn spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64` alongside the existing i64 variant. Today WFFI is i64-only; AC-3b's `rt_gemm_add(double*, double*, double*, i64, i64, i64) -> void` works through pointer args beca | [spec](doc/02_requirements/feature/runtime_api_block_sugar_plugins.md) |

### riscv (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-RISCV-HAL-PROD-WIRING-2026-05-02 | FR-RISCV-HAL-PROD-WIRING-2026-05-02: Wire Real Production Bodies for HalSmp/HalCache | **Status: IMPLEMENTED (2026-05-10)** — AC-1 and AC-2 production bodies wired. AC-3 (PortableNumericCapabilities write-back) remains a follow-up; AC-1/AC-2 gaps are closed. **AC-1 (HalSmp):** `hal_smp_ipi_send` and `hal_smp_ipi_broadcast` no | - |
| FR-RISCV-TP-INIT-2026-05-02 | FR-RISCV-TP-INIT-2026-05-02: Wire tp Register at Baremetal Boot for Per-CPU Base | **Status:** Implemented (2026-05-10) ## Why AC-4 of `riscv_smp_cache_hal_phase1` requires that each hart writes its per-CPU base address into the `tp` (thread pointer / x4) register before entering the kernel entry point.  The production he | - |

### rsa (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| RSA_PSS_PURE_SIMPLE_MODEXP_PERF_2026_05_02 | Pure-Simple RSA modexp interpreter perf cliff |  | - |

### scilib (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| SCILIB_PERF_SUGAR | Scilib Perf-Sugar Wedge Tracker | Tracks compiler and interpreter performance and ergonomics wedges discovered during the `std.linalg` / `std.ndarray` / `std.df` / `std.ml` port. Append new entries as you hit them during implementation. **Scope:** disjoint from Fortran/CUDA | - |

### sha512 (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| SHA512_256_FOR_DIGEST_AUTH_2026_05_02 | FR: SHA-512/256 for HTTP Digest Auth (RFC 7616) | **Date:** 2026-05-02 **Status:** FIXED (2026-05-10) **Blocks:** `src/lib/nogc_sync_mut/http/auth/digest.spl` algorithm=SHA-512-256 paths ## Problem RFC 7616 §6.4 lists three mandatory digest algorithms: MD5, SHA-256, and SHA-512-256. SHA-51 | - |

### simd (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| SIMD_INT_INTRINSICS_FOR_CRYPTO_2026_05_01 | Feature: extend SIMD surface with int bitwise / rotate / shuffle ops for crypto | **Status: CLOSED** — All phases landed (2026-05-02). No further action needed. > **AES-256 SIMD path LANDED 2026-05-02 — 14 rounds via W6-A externs.** `aes256_encrypt_block` in `src/os/crypto/aes256_gcm.spl` now wires through `simd_aes_roun | - |
| SIMD_U32X4_I64X4_INTRINSICS_2026_05_02 | FR: Vec4u32 and Vec4i64 SIMD Intrinsics | # Wave L / L4 — 2026-05-02 # **Status: IMPLEMENTED 2026-05-10** — structs, externs, wrappers, and aliases landed. ## Summary Add `rt_simd_*_u32x4` (8 ops) and `rt_simd_*_i64x4` (8 ops) extern primitives to the Rust runtime, with correspondi | - |

### simple-db (4)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SIMPLE-DB-0001 | Add ART / SP-GiST-like prefix index for text and hierarchical keys | Add a reusable in-memory prefix/radix index above the Phase 1 bitmap scans so repeated `StartsWith` and hierarchical-key lookups do not rescan full row or dentry arrays. | - |
| FR-SIMPLE-DB-0002 | Add learned index support for static sorted segments | For append-mostly or sealed sorted segments, add a learned-index experiment layer that can map probe keys to narrow candidate windows before exact scan. - explicit opt-in only | - |
| FR-SIMPLE-DB-0004 | Add vectorized posting-list / inverted-index execution | Extend the shared text-search work from token/trigram candidate extraction into actual posting-list intersection and bitmap materialization for repeated text search workloads. | - |
| FR-SIMPLE-DB-0005 | Research worst-case-optimal joins for Simple DB workloads | Evaluate whether worst-case-optimal joins fit the eventual Simple DB planner or any shared relational layer, rather than forcing that complexity into Phase 1. - research note compares representative workloads against current nested/scan pla | - |

### simple_db (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SIMPLE-DB-0003 | Add learned cardinality estimation for Simple DB planning | Once Simple DB has a real planner path, add a learned cardinality-estimation experiment that can coexist with BRIN summaries and conventional statistics. - isolated behind a planner experiment flag | - |

### simple_db_+_nvfs_shim (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-STORAGE-E2E-001 | End-to-end integration test: Simple DB WAL+pmap through NVFS shim | A single integration test that exercises the Simple DB WAL writer and pmap writer through the in-process NVFS shim together with a RamFs-backed MountTable mount at | - |

### simple_db__(examples/11_advanced/simple_db/src/engine/hot.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-HOT-001 | HOT: integrate pd_upper/pd_lower free-space check before chaining | `HotChain.try_update` currently chains a HOT update unconditionally at the logical-page-group level. A real PostgreSQL HOT update is only valid when the page has sufficient free space (pd_upper − pd_lower > tuple_size). The | - |

### simple_db__(examples/11_advanced/simple_db/src/engine/nvfs_shim.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPOSTGRE-M2-001 | Replace duplicated NVFS constants/types in nvfs_shim.spl with real cross-submodule imports | After FR-COMPILER-003 (2-pass import resolver), replace duplicated constants and types in `nvfs_shim.spl` with `use examples.nvfs.src.core.<module>.{<name>}` imports. Items in scope: `STORAGE_CLASS_DB_WAL`, `STORAGE_CLASS_META_DURABLE`, `DU | - |

### simple_db__(examples/11_advanced/simple_db/src/engine/tier_cache.spl) (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPOSTGRE-M4-001 | L2 NVMe tier cache (Aurora Optimized Reads pattern) | When a clean DRAM page is about to be evicted from `BufferPool`, write it to a DB_TEMP arena on local NVMe instead of discarding it. On subsequent page fault, | - |

### simpleos-os_build/compiler_throughput (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SOS-023 | Reduce native-build timeout on x86_64 WM entry | The x86_64 full OS native-build path should not fail because the unrelated `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` module exceeds the current per-file 60 second compilation timeout. | - |

### simpleos-os_process_lifecycle (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SOS-021 | Add safe execve argv/envp copy-in helpers | Add reusable, validated user-memory helpers for `copyin_u64` and NUL-terminated argv/envp vector copy-in. Helpers must validate each pointer, enforce argument count and byte caps, detect termination, and safely read across user mappings bef | - |
| FR-SOS-024 | Complete syscall 13 direct user-process handoff | Finish the direct syscall 13 app-launch path so a mounted app image can be built, mapped, registered as a scheduler-owned user task, enqueued from the syscall/trap path, and entered through the x86_64 user return path. The resident-manifest | - |

### simpleos-os_scheduler (4)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SOS-017 | Discover hardware scheduler topology domains | Replace the current flat default `SchedulerTopology` with hardware-discovered scheduler domains for SMT siblings, shared-cache/package groups, and NUMA nodes. The flat topology must remain the fallback for tests and early boot. | - |
| FR-SOS-018 | Add idle-path balancing and full wakeup preemption | Extend the conservative unblock/timer rebalance hooks with idle-pull balancing and fair-class wakeup preemption. Woken interactive/fair tasks should be able to preempt when their eligible virtual deadline is earlier than the current running | - |
| FR-SOS-019 | Add RT bandwidth throttling and priority inheritance | Add safety controls before exposing unrestricted realtime policy to user workloads: global/per-CPU RT bandwidth throttling and priority-inheritance mutex support for bounded priority inversion. | - |
| FR-SOS-020 | Complete deadline CBS and deadline-miss tracing | Extend deadline admission into a full EDF plus CBS runtime model with budget replenishment, per-task deadline-miss counters, and scheduler trace events. - [x] Runtime budget is consumed and replenished by period/deadline rules. | - |

### simpleos-os_sosix_sharing (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SOS-022 | Populate dataset_create_from_file from VFS bytes | Change `dataset_create_from_file(fd, offset, len, flags)` from an ABI-shaped sealed-handle stub into a real immutable byte snapshot populated from the VFS or open-file-description layer. | - |

### simpleos-os_x86_32 (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SOS-025 | Bring x86_32 from boot-probe target to full OS parity | Treat x86_32 as a documented boot/probe target until it has the same observable OS surface as the x86_64 lane. Do not mark x86_32 as a full OS target until it can boot, enter protected/user execution paths, run the syscall/process/shell/sto | - |

### simpleos_pci/device_grants,_dma_syscalls,_and_net_backend_layer (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0009 | Gate SR-IOV and DMA on IOMMU-capable isolation | SR-IOV virtual functions and high-throughput DMA paths must only be exposed to user-space or exoskeleton drivers when the device grant includes an isolation domain. No-IOMMU systems may use trusted early-boot drivers, but must not advertise | - |

### simpleos_pci/device_manager_and_network_backend_capability_layer (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-NET-0005 | Add SR-IOV VF discovery and assignment hooks | Discover SR-IOV-capable NIC physical functions, expose virtual function capabilities to the network backend layer, and allow explicit VF assignment to a net service or exoskeleton worker. | - |

### spipe_fine-tune_readiness_gate (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPIPE-LLM-0002 | Require target-reaching eval before acceptance | Do not accept the MedGemma artifact until recorded | - |

### spipe_llm_fine-tune_retry_loop_/_medgemma_korean (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SPIPE-LLM-0001 | Run fixed-format/data-quality retry | Execute the retry attempt | - |

### sspec-manual (4)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-SSPEC-MANUAL-0001 | Add scenario-step manual metadata | Support docgen metadata for `@step`, `@prev`, | - |
| FR-SSPEC-MANUAL-0002 | Add typed capture and evidence artifacts | Replace screenshot-only thinking with a shared | - |
| FR-SSPEC-MANUAL-0003 | Add checker/capture helper library | Provide a shared checker/capture library so `Then_*` | - |
| FR-SSPEC-MANUAL-0004 | Upgrade all generated SSpec docs to manual quality | Iteratively improve existing SPipe/SSpec tests so | - |

### static (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| STATIC_FILE_COMPRESSION_CACHE_INTEGRATION_2026_05_01 | Wire StaticCompressionCache into StaticFileHandler.handle() | **Status: LANDED 2026-05-01** — `StaticFileHandler.handle()` now consults a default-constructed `StaticCompressionCache` for files <= 64 KiB; cache miss compresses + stores, cache hit serves bytes with `Content-Encoding` + `Vary: Accept-Enc | - |

### storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) (3)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-STORAGE-0001 | Fat32Driver: statfs() and truncate/ftruncate not implemented | `Fat32Driver.statfs()` currently returns `pass_todo`. The missing piece is in `src/os/services/fat32/fat32.spl` (class `Fat32Driver`): after `mount()` the geometry fields (`total_clusters`, `sectors_per_cluster`, `bytes_per_sector`) are pop | - |
| FR-STORAGE-0002 | Fat32Driver: true pread/pwrite (cursor-preserving positional I/O) | `FsDriver.pread(handle, offset, buf)` must not advance the file cursor — it is a POSIX `pread(2)` semantics requirement. The current `Fat32Driver` in `src/os/services/fat32/fat32.spl` lacks cursor-save/restore around seek+read. `Fat32OpenFi | - |
| FR-STORAGE-0003 | Fat32Driver: fstat(FileHandle) and readdir(DirHandle) via handle | `FsDriver.fstat(FileHandle)` and `FsDriver.readdir(DirHandle)` both receive opaque handles, not paths. The wrapper in `fat32_stub.spl` maintains a `file_handles: [Fat32HandleEntry]` table with `path: text` per entry, so the information is p | - |

### test/fixtures/features/ (1)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| FR-BDD-WAVE7-8-001 | BDD feature files for wave 7/8 storage work | MDSOC+ requires BDD specs for new functionality before or alongside impl. Wave 7/8 added AES-GCM encryption (N6a), raw send/receive (N6b), scrub detect+repair | - |

---

## Progress by Category

| Category | Total | Complete | Pending | % Complete |
|----------|-------|----------|---------|------------|
| `app/editor`_+_`lib/editor` | 1 | 0 | 1 | 0.0% |
| `app/editor`_+_`lib/editor`_+_seed_runtime/jit | 1 | 0 | 1 | 0.0% |
| `simple_web_html_layout_renderer.spl` | 1 | 0 | 1 | 0.0% |
| `simple_web_html_layout_renderer.spl`_+_`browser_renderer.spl` | 1 | 0 | 1 | 0.0% |
| `src/compiler/70.backend/linker/lib_smf.spl`_+_codegen | 1 | 0 | 1 | 0.0% |
| `src/compiler_rust/compiler/src/codegen/instr/core.rs`_+_hir | 1 | 0 | 1 | 0.0% |
| `src/compiler_rust/compiler/src/hir/lower/*`, | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/http_server/` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/io/`_and_runtime_backend_adapters | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/io/connection_pool.spl` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/io/packet_ring.spl` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/io/scatter_gather.spl` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_async_mut/io/socket_options.spl` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl`_+_`gpu_driver/driver_adapter.spl` | 1 | 0 | 1 | 0.0% |
| `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl`_+ | 1 | 0 | 1 | 0.0% |
| `src/os/drivers/framebuffer/`,_`src/os/drivers/virtio/virtio_gpu.spl`, | 1 | 0 | 1 | 0.0% |
| `src/os/services/netstack/`_and_`src/os/posix/socket_compat.spl` | 1 | 0 | 1 | 0.0% |
| `src/os/services/netstack/tcp_connection.spl` | 1 | 0 | 1 | 0.0% |
| `src/os/userlib/device.spl`,_`src/os/kernel/ipc/syscall.spl`, | 1 | 0 | 1 | 0.0% |
| `src/os/userlib/device.spl`,_network_drivers,_block_drivers,_and | 1 | 0 | 1 | 0.0% |
| `src/runtime/startup/baremetal/<arch>/`_+_`src/hardware/<arch>/` | 1 | 0 | 1 | 0.0% |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/` | 1 | 0 | 1 | 0.0% |
| async_http_server,_memory_registration,_and_network_backend_layer | 1 | 0 | 1 | 0.0% |
| compiler | 1 | 0 | 1 | 0.0% |
| compiler_(cranelift_jit_/_hir_lowering) | 1 | 0 | 1 | 0.0% |
| compiler_+_`src/lib/common/ui/`_+_browser_renderer | 1 | 0 | 1 | 0.0% |
| compiler_+_domain_library | 2 | 0 | 2 | 0.0% |
| compiler_+_geometry/domain_library | 1 | 0 | 1 | 0.0% |
| compiler_+_std_schema_tooling | 1 | 0 | 1 | 0.0% |
| compiler_loader_surfaces_in_`src/compiler/99.loader/` | 1 | 0 | 1 | 0.0% |
| compiler_—_`src/compiler/20.hir/hir_lowering/`_+_`src/compiler/80.driver/` | 1 | 0 | 1 | 0.0% |
| compiler_—_`src/compiler/20.hir/hir_types.spl`_+_`src/compiler/20.hir/hir_lowering/` | 1 | 0 | 1 | 0.0% |
| compiler_—_import_resolver_/_name-resolution_pass | 1 | 0 | 1 | 0.0% |
| compiler_—_parser,_ast,_tree-sitter_outline,_hir_metadata | 1 | 0 | 1 | 0.0% |
| crypto_/_interpreter_perf | 1 | 0 | 1 | 0.0% |
| driver_/_compiler_frontend_+_hir_lowering | 1 | 0 | 1 | 0.0% |
| ecdsa | 1 | 0 | 1 | 0.0% |
| engine2d | 1 | 0 | 1 | 0.0% |
| hkdf | 1 | 0 | 1 | 0.0% |
| https | 1 | 0 | 1 | 0.0% |
| kv260-simple-rv64-network | 1 | 0 | 1 | 0.0% |
| lexer_+_parser_+_hir_+_struct_layout | 1 | 0 | 1 | 0.0% |
| llm-backed_medical_qa_app/server_handoff | 1 | 0 | 1 | 0.0% |
| lzma2 | 1 | 0 | 1 | 0.0% |
| network_tests,_qemu_scenarios,_and_smoke_scripts | 1 | 0 | 1 | 0.0% |
| nvfs | 10 | 0 | 10 | 0.0% |
| nvfs__(src/os/services/nvfs/src/core/arena.spl_or_new_constants.spl) | 1 | 0 | 1 | 0.0% |
| nvfs__(src/os/services/nvfs/src/core/compression.spl_—_new) | 1 | 0 | 1 | 0.0% |
| nvfs__(src/os/services/nvfs/src/core/dedup.spl_—_new) | 1 | 0 | 1 | 0.0% |
| nvfs__(src/os/services/nvfs/src/core/encryption.spl) | 2 | 0 | 2 | 0.0% |
| nvfs__(src/os/services/nvfs/src/core/encryption.spl_+_arena.spl) | 1 | 0 | 1 | 0.0% |
| nvme,_virtio-blk,_vfs/fs-driver_interface | 1 | 0 | 1 | 0.0% |
| os-kernel_(src/os/kernel/ipc/spm_port.spl_+ | 1 | 0 | 1 | 0.0% |
| os-kernel_(src/os/kernel/ipc/syscall.spl_+ | 1 | 0 | 1 | 0.0% |
| os-kernel_(src/os/kernel/ipc_+_src/os/kernel/memory) | 1 | 0 | 1 | 0.0% |
| os__(src/os/kernel/acpi/) | 1 | 0 | 1 | 0.0% |
| os__(src/os/services/vfs/vfs_init.spl) | 1 | 0 | 1 | 0.0% |
| p256 | 1 | 0 | 1 | 0.0% |
| parser_/_`src/compiler/` | 1 | 0 | 1 | 0.0% |
| plugin | 3 | 0 | 3 | 0.0% |
| plugin_/_15.blocks | 1 | 0 | 1 | 0.0% |
| plugin_/_15.blocks_/_10.frontend.desugar | 1 | 0 | 1 | 0.0% |
| plugin_/_70.backend.cranelift | 1 | 0 | 1 | 0.0% |
| plugin_/_compiler_/_di | 1 | 0 | 1 | 0.0% |
| plugin_/_runtime | 1 | 0 | 1 | 0.0% |
| riscv | 2 | 0 | 2 | 0.0% |
| rsa | 1 | 0 | 1 | 0.0% |
| scilib | 1 | 0 | 1 | 0.0% |
| sha512 | 1 | 0 | 1 | 0.0% |
| simd | 2 | 0 | 2 | 0.0% |
| simple-db | 4 | 0 | 4 | 0.0% |
| simple_db | 1 | 0 | 1 | 0.0% |
| simple_db_+_nvfs_shim | 1 | 0 | 1 | 0.0% |
| simple_db__(examples/11_advanced/simple_db/src/engine/hot.spl) | 1 | 0 | 1 | 0.0% |
| simple_db__(examples/11_advanced/simple_db/src/engine/nvfs_shim.spl) | 1 | 0 | 1 | 0.0% |
| simple_db__(examples/11_advanced/simple_db/src/engine/tier_cache.spl) | 1 | 0 | 1 | 0.0% |
| simpleos-os_build/compiler_throughput | 1 | 0 | 1 | 0.0% |
| simpleos-os_process_lifecycle | 2 | 0 | 2 | 0.0% |
| simpleos-os_scheduler | 4 | 0 | 4 | 0.0% |
| simpleos-os_sosix_sharing | 1 | 0 | 1 | 0.0% |
| simpleos-os_x86_32 | 1 | 0 | 1 | 0.0% |
| simpleos_pci/device_grants,_dma_syscalls,_and_net_backend_layer | 1 | 0 | 1 | 0.0% |
| simpleos_pci/device_manager_and_network_backend_capability_layer | 1 | 0 | 1 | 0.0% |
| spipe_fine-tune_readiness_gate | 1 | 0 | 1 | 0.0% |
| spipe_llm_fine-tune_retry_loop_/_medgemma_korean | 1 | 0 | 1 | 0.0% |
| sspec-manual | 4 | 0 | 4 | 0.0% |
| static | 1 | 0 | 1 | 0.0% |
| storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | 3 | 0 | 3 | 0.0% |
| test/fixtures/features/ | 1 | 0 | 1 | 0.0% |

---

## Implementation Priority

### Critical (Do First)

### High (Next Sprint)
3. Planned features with dependencies

### Medium (Backlog)
4. Remaining planned features (116 features)

### Low (Future)
