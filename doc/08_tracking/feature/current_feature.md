# Current Features

**Database:** `doc/08_tracking/feature/feature_db.sdn`

| ID | Group | Priority | Title | Requirement | External |
|----|-------|----------|-------|-------------|----------|
| FR-COMPILER-012 | compiler_(cranelift_jit_/_hir_lowering) | P2 | JIT-compile pure-Simple software rendering loops (unblock high-DPI 2D) | - | - |
| FR-COMPILER-002 | compiler_—_import_resolver_/_name-resolution_pass | P0 | Fix self-hosted import resolver: same-named structs in different modules shadow each other | - | [link](FR-COMPILER-001 (upstream symptom)) |
| FR-COMPILER-003 | compiler_—_`src/compiler/20.hir/hir_lowering/`_+_`src/compiler/80.driver/` | P0 | Add 2-pass import resolver to self-hosted HIR lowering | - | [link](FR-COMPILER-002 (parent), FR-COMPILER-001 (upstream symptom)) |
| FR-COMPILER-001 | compiler | P1 | Fix self-hosted binary missing CompileOptions field accessors | - | - |
| FR-COMPILER-004 | compiler_—_`src/compiler/20.hir/hir_types.spl`_+_`src/compiler/20.hir/hir_lowering/` | P0 | Module-scoped symbol tables for correct cross-module name isolation | - | [link](FR-COMPILER-002, FR-COMPILER-003 (prerequisites and parent)) |
| FR-COMPILER-005 | compiler_—_parser,_ast,_tree-sitter_outline,_hir_metadata | P0 | Add raw top-level domain block carrier | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-006 | compiler_+_std_schema_tooling | P0 | Implement schema{} contracts and compatibility checks | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-007 | compiler_+_`src/lib/common/ui/`_+_browser_renderer | P1 | Add style{} and ui{} authoring surfaces | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-008 | compiler_+_domain_library | P1 | Add music{} authoring with MusicXML interchange | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-009 | compiler_+_domain_library | P1 | Add bim{} and city{} standards bindings | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-010 | compiler_+_geometry/domain_library | P2 | Add cad{} parametric authoring and STEP AP242 export | [link](doc/02_requirements/feature/all_regions.md) | - |
| FR-COMPILER-011 | compiler_loader_surfaces_in_`src/compiler/99.loader/` | P1 | Share loader core logic only across proven safe seams | - | - |
| FR-COMPILER-012-2 | parser_/_`src/compiler/` | P2 | FR-COMPILER-012 — Fix `expect (expr) == val` parser precedence | - | - |
| FR-DRIVER-0001 | driver_/_compiler_frontend_+_hir_lowering | P1 | Compiler sugar for `@driver(...)` and `@native_lib(...)` attributes | - | - |
| FR-DRIVER-0002 | `src/compiler_rust/compiler/src/codegen/instr/core.rs`_+_hir | P1 | Cranelift `>>` backend fix (disambiguation + signedness) | - | - |
| FR-DRIVER-0004 | `src/compiler/70.backend/linker/lib_smf.spl`_+_codegen | P1 | `.drv_manifest` SMF section + emission from `@driver` attribute | - | - |
| FR-DRIVER-0005 | `src/runtime/startup/baremetal/<arch>/`_+_`src/hardware/<arch>/` | P1 | Per-arch DMA cache-maintenance runtime (6 arches) | - | - |
| FR-DRIVER-0006 | `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl`_+_`gpu_driver/driver_adapter.spl` | P2 | Real `fs_driver` + `gpu_driver` adapter integration | - | - |
| FR-DRIVER-0007 | `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl`_+ | P2 | Port `Fat32Core` + `BlockDevice` into `src/lib/nogc_sync_mut/fs_driver/` to unblock FS adapter forwarding | - | - |
| FR-DRIVER-0008 | `src/compiler_rust/compiler/src/hir/lower/*`, | P2 (blocks FR-DRIVER-0003) | Rust-seed bitfield HIR/MIR/sema codegen (blocker for FR-0003) | - | - |
| FR-DRIVER-0009 | `src/os/userlib/device.spl`,_`src/os/kernel/ipc/syscall.spl`, | P1 | Shared DMA descriptor contract for net, file, and display drivers | - | - |
| FR-DRIVER-0010 | nvme,_virtio-blk,_vfs/fs-driver_interface | P1 | DMA-backed file/block driver direct I/O path | - | - |
| FR-DRIVER-0011 | `src/os/drivers/framebuffer/`,_`src/os/drivers/virtio/virtio_gpu.spl`, | P1 | VGA/BGA framebuffer and VirtIO-GPU DMA acceleration boundary | - | - |
| EDITOR_TUI_RENDER_COMPLETION_2026_05_29 | `app/editor`_+_`lib/editor`_+_seed_runtime/jit | medium | Editor TUI render completion + ctrl module consolidation | - | - |
| FR-KV260-NET-0001 | kv260-simple-rv64-network | P0 | Verify SimpleOS RV64 web and SSH on KV260 FPGA | - | - |
| LZMA2_FULL_LCLPPB_2026_05_01 | lzma2 | P2 | LZMA2 — Full LC/LP/PB Property Support | - | - |
| FR-NET-0001 | `src/os/services/netstack/`_and_`src/os/posix/socket_compat.spl` | P0 | Add connect completion and nonblocking socket semantics | - | - |
| FR-NET-0002 | `src/os/services/netstack/tcp_connection.spl` | P0 | Complete TCP data path wakeups and close/error semantics | - | - |
| FR-NET-0003 | `src/lib/nogc_async_mut/http_server/` | P1 | Route HTTP static files through capability-driven sendfile | - | - |
| FR-NET-0004 | `src/lib/nogc_async_mut/io/`_and_runtime_backend_adapters | P1 | Add packet I/O backend boundary for AF_XDP or DPDK | - | - |
| FR-NET-0005 | simpleos_pci/device_manager_and_network_backend_capability_layer | P2 | Add SR-IOV VF discovery and assignment hooks | - | - |
| FR-NET-0006 | async_http_server,_memory_registration,_and_network_backend_layer | P2 | Prototype RDMA/exoskeleton transport for web serving | - | - |
| FR-NET-0007 | network_tests,_qemu_scenarios,_and_smoke_scripts | P1 | Add network performance and timeout verification harness | - | - |
| FR-NET-0008 | `src/os/userlib/device.spl`,_network_drivers,_block_drivers,_and | P1 | Share DMA buffer ownership with storage and display drivers | - | - |
| FR-NET-0009 | simpleos_pci/device_grants,_dma_syscalls,_and_net_backend_layer | P1 | Gate SR-IOV and DMA on IOMMU-capable isolation | - | - |
| FR-NET-0010 | `src/lib/nogc_async_mut/io/packet_ring.spl` | P1 | Add bounded ring-buffer data structure for packet RX/TX paths | - | - |
| FR-NET-0011 | `src/lib/nogc_async_mut/io/scatter_gather.spl` | P1 | Add scatter-gather I/O list types | - | - |
| FR-NET-0012 | `src/lib/nogc_async_mut/io/socket_options.spl` | P1 | Add async TCP socket option record types | - | - |
| FR-NET-0013 | `src/lib/nogc_async_mut/io/connection_pool.spl` | P1 | Add TCP connection pool for HTTP keep-alive reuse | - | - |
| FR-STORAGE-0001 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | P1 | Fat32Driver: statfs() and truncate/ftruncate not implemented | - | - |
| FR-STORAGE-0002 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | P2 | Fat32Driver: true pread/pwrite (cursor-preserving positional I/O) | - | - |
| FR-STORAGE-0003 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | P1 | Fat32Driver: fstat(FileHandle) and readdir(DirHandle) via handle | - | - |
| FR-STORAGE-0004 | nvfs | P1 | MountTable.resolve() uses slice() which is broken in baremetal Cranelift | - | - |
| FR-HOT-001 | simple_db__(examples/11_advanced/simple_db/src/engine/hot.spl) | P2 | HOT: integrate pd_upper/pd_lower free-space check before chaining | - | - |
| FR-BENCH-CLOCK-002 | nvfs | P2 | Replace PIT-ch2 TSC calibration with HPET/PMTMR | - | - |
| FR-SIMPLEOS-ACPI-001 | os__(src/os/kernel/acpi/) | P1 | ACPI table walker (RSDP → RSDT/XSDT → FADT + HPET) | - | - |
| FR-SIMPLEOS-M5-001 | os__(src/os/services/vfs/vfs_init.spl) | P1 | VFS select-file cursor semantic (VfsCursor singleton) | - | - |
| FR-NVFS-N4a-001 | nvfs | P1 | Scrub repair path: detect + repair from reflink peers | - | - |
| FR-NVFS-N4b-001 | nvfs | P2 | Proactive scrub scheduler + META_DURABLE replica repair | - | - |
| FR-N3-001 | nvfs | P1 | Replace flat pmap sidecar with B-tree keyed by (arena_id, offset) | - | - |
| FR-NVFS-N5b-001 | nvfs | P2 | B-tree rebalancing on delete (merge / rotate) | - | - |
| FR-BENCH-CLOCK-001 | nvfs | P1 | Add rt_time_now_ns() for hosted and baremetal targets | - | - |
| FR-NVFS-N6a-001 | nvfs__(src/os/services/nvfs/src/core/encryption.spl) | P1 | Wire real AES-128-GCM into NVFS leaf DEK encrypt/decrypt | - | - |
| FR-NVFS-N6a-002 | nvfs__(src/os/services/nvfs/src/core/encryption.spl) | P1 | KDF hardening: salted derivation for per-arena dataset keys | - | - |
| FR-NVFS-N6a-003 | nvfs__(src/os/services/nvfs/src/core/encryption.spl_+_arena.spl) | P1 | DEK rotation on arena seal | - | - |
| FR-NVFS-N6b-001 | nvfs | P1 | Raw send / encrypted replication stream (btrfs-send style) | - | - |
| FR-NVFS-N7a-001 | nvfs__(src/os/services/nvfs/src/core/compression.spl_—_new) | P2 | Inline compression: per-arena LZ4/Zstd, class-aware defaults | - | - |
| FR-NVFS-N7b-001 | nvfs__(src/os/services/nvfs/src/core/dedup.spl_—_new) | P2 | Inline deduplication: content-addressable DDT extending reflink machinery | - | - |
| FR-BDD-WAVE7-8-001 | test/fixtures/features/ | P1 | BDD feature files for wave 7/8 storage work | - | - |
| FR-SPOSTGRE-M4-001 | simple_db__(examples/11_advanced/simple_db/src/engine/tier_cache.spl) | P1 | L2 NVMe tier cache (Aurora Optimized Reads pattern) | - | - |
| FR-STORAGE-E2E-001 | simple_db_+_nvfs_shim | P1 | End-to-end integration test: Simple DB WAL+pmap through NVFS shim | - | - |
| FR-BENCH-BASELINE-001 | nvfs | P1 | Run bench harness with real clock and record baseline numbers | - | [link](FR-BENCH-ARENA-ITER-001) |
| FR-BENCH-ARENA-ITER-001 | nvfs | P2 | Reduce nvfs_arena_throughput iter counts for interpreter budget | - | [link](FR-BENCH-BASELINE-001) |
| FR-SPOSTGRE-M2-001 | simple_db__(examples/11_advanced/simple_db/src/engine/nvfs_shim.spl) | P1 | Replace duplicated NVFS constants/types in nvfs_shim.spl with real cross-submodule imports | - | [link](FR-COMPILER-003 (prerequisite, Implemented 2026-04-18)) |
| FR-SPOSTGRE-M2-002 | nvfs__(src/os/services/nvfs/src/core/arena.spl_or_new_constants.spl) | P2 | Add named StorageClass and DurabilityClass constants to NVFS core | - | [link](FR-SPOSTGRE-M2-001 (parent)) |
| FR-PLUG-0001 | plugin_/_runtime | P1 | WFFI f64 calling-convention extern | [link](doc/02_requirements/feature/runtime_api_block_sugar_plugins.md) | - |
| FR-PLUG-0005 | plugin_/_compiler_/_di | P1 | DI runtime-slot plugin loader integration | - | - |
| FR-CRYPTO-0001 | crypto_/_interpreter_perf | P1 | RSA-2048 modexp completes within interpreter test budget | - | - |
| FR-SIMPLE-DB-0001 | simple-db | P1 | Add ART / SP-GiST-like prefix index for text and hierarchical keys | - | - |
| FR-SIMPLE-DB-0002 | simple-db | P2 | Add learned index support for static sorted segments | - | - |
| FR-SIMPLE-DB-0003 | simple_db | P2 | Add learned cardinality estimation for Simple DB planning | - | - |
| FR-SIMPLE-DB-0004 | simple-db | P1 | Add vectorized posting-list / inverted-index execution | - | - |
| FR-SIMPLE-DB-0005 | simple-db | P2 | Research worst-case-optimal joins for Simple DB workloads | - | - |
| FR-SOS-025 | simpleos-os_x86_32 | P2 | Bring x86_32 from boot-probe target to full OS parity | - | - |
| FR-SOS-017 | simpleos-os_scheduler | P1 | Discover hardware scheduler topology domains | - | - |
| FR-SOS-018 | simpleos-os_scheduler | P1 | Add idle-path balancing and full wakeup preemption | - | - |
| FR-SOS-019 | simpleos-os_scheduler | P1 | Add RT bandwidth throttling and priority inheritance | - | - |
| FR-SOS-020 | simpleos-os_scheduler | P1 | Complete deadline CBS and deadline-miss tracing | - | - |
| FR-SOS-021 | simpleos-os_process_lifecycle | P1 | Add safe execve argv/envp copy-in helpers | - | - |
| FR-SOS-022 | simpleos-os_sosix_sharing | P1 | Populate dataset_create_from_file from VFS bytes | - | - |
| FR-SOS-023 | simpleos-os_build/compiler_throughput | P1 | Reduce native-build timeout on x86_64 WM entry | - | - |
| FR-SOS-024 | simpleos-os_process_lifecycle | P0 | Complete syscall 13 direct user-process handoff | - | - |
| FR-SPM-0001 | os-kernel_(src/os/kernel/ipc_+_src/os/kernel/memory) | P2 | Page-table-walk read primitive for cross-page / non-identity-physmap user reads | - | - |
| FR-SPM-0002 | os-kernel_(src/os/kernel/ipc/syscall.spl_+ | P2 | Caller-TaskId → privilege-mirror lookup for `sys_priv_check` (case 110) | - | - |
| FR-SPM-0003 | os-kernel_(src/os/kernel/ipc/spm_port.spl_+ | P2 | Rebind syscall for SPM port when real SPM task id is known | - | - |
| FR-SSPEC-MANUAL-0001 | sspec-manual | P1 | Add scenario-step manual metadata | - | - |
| FR-SSPEC-MANUAL-0002 | sspec-manual | P1 | Add typed capture and evidence artifacts | - | - |
| FR-SSPEC-MANUAL-0003 | sspec-manual | P1 | Add checker/capture helper library | - | - |
| FR-SSPEC-MANUAL-0004 | sspec-manual | P2 | Upgrade all generated SSpec docs to manual quality | - | - |
| LOW_DEPENDENCY_UI_DYNSMF_2026_06_05 | ui | P1 | Refactor UI dependencies and load stdlib-like dynSMF libraries | [link](doc/02_requirements/feature/low_dependency_ui_dynsmf.md; doc/02_requirements/nfr/low_dependency_ui_dynsmf.md) | - |
| BROWSER_WASM_WEBGPU_INFRA_2026_06_13 | browser_webgpu | P0 | Implement browser WASM and WebGPU infrastructure | [link](doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md; doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md) | - |
| SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16 | ui_web | P0 | Harden Simple Web browser production boundary | [link](doc/02_requirements/feature/simple_web_browser_production_hardening.md; doc/02_requirements/nfr/simple_web_browser_production_hardening.md) | - |
| FR-RUNTIME-MULTICORE-GREEN-2026-06-06 | runtime_concurrency | P0 | Support Go-like M:N multicore green work | [link](doc/02_requirements/feature/multicore_green.md; doc/02_requirements/nfr/multicore_green.md) | - |
| FR-LLM-TOOLING-0001 | llm_tooling_context_ponytail_mimic | P1 | Replace external context/Ponytail paths with Simple-owned surfaces | [link](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md; doc/02_requirements/nfr/llm_tooling_context_ponytail_mimic.md) | - |
| FR-LLM-DASHBOARD-0001 | kairos_like_simple_mcp_llm_dashboard | P1 | Harden assistant dashboard and operator evidence | [link](doc/02_requirements/app/dashboard/kairos_like_simple_mcp_llm_dashboard.md; doc/02_requirements/nfr/kairos_like_simple_mcp_llm_dashboard.md) | - |
