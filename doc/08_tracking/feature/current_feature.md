# Current Features

| ID | Group | Title | Requirement |
|----|-------|-------|-------------|
| EDITOR_TUI_RENDER_COMPLETION_2026_05_29 | `app/editor`_+_`lib/editor`_+_seed_runtime/jit | Editor TUI render completion + ctrl module consolidation | - |
| FR-BDD-WAVE7-8-001 | test/fixtures/features/ | BDD feature files for wave 7/8 storage work | - |
| FR-BENCH-ARENA-ITER-001 | nvfs | Reduce nvfs_arena_throughput iter counts for interpreter budget | - |
| FR-BENCH-BASELINE-001 | nvfs | Run bench harness with real clock and record baseline numbers | - |
| FR-BENCH-CLOCK-001 | nvfs | Add rt_time_now_ns() for hosted and baremetal targets | - |
| FR-BENCH-CLOCK-002 | nvfs | Replace PIT-ch2 TSC calibration with HPET/PMTMR | - |
| BROWSER_WASM_WEBGPU_INFRA_2026_06_13 | browser_webgpu | Implement browser WASM and WebGPU infrastructure | [feature options](doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md); [NFR options](doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md) |
| FR-COMPILER-001 | compiler | Fix self-hosted binary missing CompileOptions field accessors | - |
| FR-COMPILER-002 | compiler_—_import_resolver_/_name-resolution_pass | Fix self-hosted import resolver: same-named structs in different modules shadow each other | - |
| FR-COMPILER-003 | compiler_—_`src/compiler/20.hir/hir_lowering/`_+_`src/compiler/80.driver/` | Add 2-pass import resolver to self-hosted HIR lowering | - |
| FR-COMPILER-004 | compiler_—_`src/compiler/20.hir/hir_types.spl`_+_`src/compiler/20.hir/hir_lowering/` | Module-scoped symbol tables for correct cross-module name isolation | - |
| FR-COMPILER-005 | compiler_—_parser,_ast,_tree-sitter_outline,_hir_metadata | Add raw top-level domain block carrier | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-006 | compiler_+_std_schema_tooling | Implement schema{} contracts and compatibility checks | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-007 | compiler_+_`src/lib/common/ui/`_+_browser_renderer | Add style{} and ui{} authoring surfaces | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-008 | compiler_+_domain_library | Add music{} authoring with MusicXML interchange | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-009 | compiler_+_domain_library | Add bim{} and city{} standards bindings | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-010 | compiler_+_geometry/domain_library | Add cad{} parametric authoring and STEP AP242 export | [link](doc/02_requirements/feature/all_regions.md) |
| FR-COMPILER-011 | compiler_loader_surfaces_in_`src/compiler/99.loader/` | Share loader core logic only across proven safe seams | - |
| FR-COMPILER-012 | compiler_(cranelift_jit_/_hir_lowering) | JIT-compile pure-Simple software rendering loops (unblock high-DPI 2D) | - |
| FR-COMPILER-012-2 | parser_/_`src/compiler/` | FR-COMPILER-012 — Fix `expect (expr) == val` parser precedence | - |
| FR-CRYPTO-0001 | crypto_/_interpreter_perf | RSA-2048 modexp completes within interpreter test budget | - |
| FR-DRIVER-0001 | driver_/_compiler_frontend_+_hir_lowering | Compiler sugar for `@driver(...)` and `@native_lib(...)` attributes | - |
| FR-DRIVER-0002 | `src/compiler_rust/compiler/src/codegen/instr/core.rs`_+_hir | Cranelift `>>` backend fix (disambiguation + signedness) | - |
| FR-DRIVER-0004 | `src/compiler/70.backend/linker/lib_smf.spl`_+_codegen | `.drv_manifest` SMF section + emission from `@driver` attribute | - |
| FR-DRIVER-0005 | `src/runtime/startup/baremetal/<arch>/`_+_`src/hardware/<arch>/` | Per-arch DMA cache-maintenance runtime (6 arches) | - |
| FR-DRIVER-0006 | `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl`_+_`gpu_driver/driver_adapter.spl` | Real `fs_driver` + `gpu_driver` adapter integration | - |
| FR-DRIVER-0007 | `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl`_+ | Port `Fat32Core` + `BlockDevice` into `src/lib/nogc_sync_mut/fs_driver/` to unblock FS adapter forwarding | - |
| FR-DRIVER-0008 | `src/compiler_rust/compiler/src/hir/lower/*`, | Rust-seed bitfield HIR/MIR/sema codegen (blocker for FR-0003) | - |
| FR-DRIVER-0009 | `src/os/userlib/device.spl`,_`src/os/kernel/ipc/syscall.spl`, | Shared DMA descriptor contract for net, file, and display drivers | - |
| FR-DRIVER-0010 | nvme,_virtio-blk,_vfs/fs-driver_interface | DMA-backed file/block driver direct I/O path | - |
| FR-DRIVER-0011 | `src/os/drivers/framebuffer/`,_`src/os/drivers/virtio/virtio_gpu.spl`, | VGA/BGA framebuffer and VirtIO-GPU DMA acceleration boundary | - |
| FR-HOT-001 | simple_db__(examples/11_advanced/simple_db/src/engine/hot.spl) | HOT: integrate pd_upper/pd_lower free-space check before chaining | - |
| FR-KV260-NET-0001 | kv260-simple-rv64-network | Verify SimpleOS RV64 web and SSH on KV260 FPGA | - |
| FR-N3-001 | nvfs | Replace flat pmap sidecar with B-tree keyed by (arena_id, offset) | - |
| FR-NET-0001 | `src/os/services/netstack/`_and_`src/os/posix/socket_compat.spl` | Add connect completion and nonblocking socket semantics | - |
| FR-NET-0002 | `src/os/services/netstack/tcp_connection.spl` | Complete TCP data path wakeups and close/error semantics | - |
| FR-NET-0003 | `src/lib/nogc_async_mut/http_server/` | Route HTTP static files through capability-driven sendfile | - |
| FR-NET-0004 | `src/lib/nogc_async_mut/io/`_and_runtime_backend_adapters | Add packet I/O backend boundary for AF_XDP or DPDK | - |
| FR-NET-0005 | simpleos_pci/device_manager_and_network_backend_capability_layer | Add SR-IOV VF discovery and assignment hooks | - |
| FR-NET-0006 | async_http_server,_memory_registration,_and_network_backend_layer | Prototype RDMA/exoskeleton transport for web serving | - |
| FR-NET-0007 | network_tests,_qemu_scenarios,_and_smoke_scripts | Add network performance and timeout verification harness | - |
| FR-NET-0008 | `src/os/userlib/device.spl`,_network_drivers,_block_drivers,_and | Share DMA buffer ownership with storage and display drivers | - |
| FR-NET-0009 | simpleos_pci/device_grants,_dma_syscalls,_and_net_backend_layer | Gate SR-IOV and DMA on IOMMU-capable isolation | - |
| FR-NET-0010 | `src/lib/nogc_async_mut/io/packet_ring.spl` | Add bounded ring-buffer data structure for packet RX/TX paths | - |
| FR-NET-0011 | `src/lib/nogc_async_mut/io/scatter_gather.spl` | Add scatter-gather I/O list types | - |
| FR-NET-0012 | `src/lib/nogc_async_mut/io/socket_options.spl` | Add async TCP socket option record types | - |
| FR-NET-0013 | `src/lib/nogc_async_mut/io/connection_pool.spl` | Add TCP connection pool for HTTP keep-alive reuse | - |
| FR-NVFS-N4a-001 | nvfs | Scrub repair path: detect + repair from reflink peers | - |
| FR-NVFS-N4b-001 | nvfs | Proactive scrub scheduler + META_DURABLE replica repair | - |
| FR-NVFS-N5b-001 | nvfs | B-tree rebalancing on delete (merge / rotate) | - |
| FR-NVFS-N6a-001 | nvfs__(src/os/services/nvfs/src/core/encryption.spl) | Wire real AES-128-GCM into NVFS leaf DEK encrypt/decrypt | - |
| FR-NVFS-N6a-002 | nvfs__(src/os/services/nvfs/src/core/encryption.spl) | KDF hardening: salted derivation for per-arena dataset keys | - |
| FR-NVFS-N6a-003 | nvfs__(src/os/services/nvfs/src/core/encryption.spl_+_arena.spl) | DEK rotation on arena seal | - |
| FR-NVFS-N6b-001 | nvfs | Raw send / encrypted replication stream (btrfs-send style) | - |
| FR-NVFS-N7a-001 | nvfs__(src/os/services/nvfs/src/core/compression.spl_—_new) | Inline compression: per-arena LZ4/Zstd, class-aware defaults | - |
| FR-NVFS-N7b-001 | nvfs__(src/os/services/nvfs/src/core/dedup.spl_—_new) | Inline deduplication: content-addressable DDT extending reflink machinery | - |
| FR-PLUG-0001 | plugin_/_runtime | WFFI f64 calling-convention extern | [link](doc/02_requirements/feature/runtime_api_block_sugar_plugins.md) |
| FR-PLUG-0005 | plugin_/_compiler_/_di | DI runtime-slot plugin loader integration | - |
| FR-SIMPLE-DB-0001 | simple-db | Add ART / SP-GiST-like prefix index for text and hierarchical keys | - |
| FR-SIMPLE-DB-0002 | simple-db | Add learned index support for static sorted segments | - |
| FR-SIMPLE-DB-0003 | simple_db | Add learned cardinality estimation for Simple DB planning | - |
| FR-SIMPLE-DB-0004 | simple-db | Add vectorized posting-list / inverted-index execution | - |
| FR-SIMPLE-DB-0005 | simple-db | Research worst-case-optimal joins for Simple DB workloads | - |
| FR-SIMPLEOS-ACPI-001 | os__(src/os/kernel/acpi/) | ACPI table walker (RSDP → RSDT/XSDT → FADT + HPET) | - |
| FR-SIMPLEOS-M5-001 | os__(src/os/services/vfs/vfs_init.spl) | VFS select-file cursor semantic (VfsCursor singleton) | - |
| FR-SOS-017 | simpleos-os_scheduler | Discover hardware scheduler topology domains | - |
| FR-SOS-018 | simpleos-os_scheduler | Add idle-path balancing and full wakeup preemption | - |
| FR-SOS-019 | simpleos-os_scheduler | Add RT bandwidth throttling and priority inheritance | - |
| FR-SOS-020 | simpleos-os_scheduler | Complete deadline CBS and deadline-miss tracing | - |
| FR-SOS-021 | simpleos-os_process_lifecycle | Add safe execve argv/envp copy-in helpers | - |
| FR-SOS-022 | simpleos-os_sosix_sharing | Populate dataset_create_from_file from VFS bytes | - |
| FR-SOS-023 | simpleos-os_build/compiler_throughput | Reduce native-build timeout on x86_64 WM entry | - |
| FR-SOS-024 | simpleos-os_process_lifecycle | Complete syscall 13 direct user-process handoff | - |
| FR-SOS-025 | simpleos-os_x86_32 | Bring x86_32 from boot-probe target to full OS parity | - |
| FR-SPM-0001 | os-kernel_(src/os/kernel/ipc_+_src/os/kernel/memory) | Page-table-walk read primitive for cross-page / non-identity-physmap user reads | - |
| FR-SPM-0002 | os-kernel_(src/os/kernel/ipc/syscall.spl_+ | Caller-TaskId → privilege-mirror lookup for `sys_priv_check` (case 110) | - |
| FR-SPM-0003 | os-kernel_(src/os/kernel/ipc/spm_port.spl_+ | Rebind syscall for SPM port when real SPM task id is known | - |
| FR-SPOSTGRE-M2-001 | simple_db__(examples/11_advanced/simple_db/src/engine/nvfs_shim.spl) | Replace duplicated NVFS constants/types in nvfs_shim.spl with real cross-submodule imports | - |
| FR-SPOSTGRE-M2-002 | nvfs__(src/os/services/nvfs/src/core/arena.spl_or_new_constants.spl) | Add named StorageClass and DurabilityClass constants to NVFS core | - |
| FR-SPOSTGRE-M4-001 | simple_db__(examples/11_advanced/simple_db/src/engine/tier_cache.spl) | L2 NVMe tier cache (Aurora Optimized Reads pattern) | - |
| FR-SSPEC-MANUAL-0001 | sspec-manual | Add scenario-step manual metadata | - |
| FR-SSPEC-MANUAL-0002 | sspec-manual | Add typed capture and evidence artifacts | - |
| FR-SSPEC-MANUAL-0003 | sspec-manual | Add checker/capture helper library | - |
| FR-SSPEC-MANUAL-0004 | sspec-manual | Upgrade all generated SSpec docs to manual quality | - |
| FR-STORAGE-0001 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | Fat32Driver: statfs() and truncate/ftruncate not implemented | - |
| FR-STORAGE-0002 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | Fat32Driver: true pread/pwrite (cursor-preserving positional I/O) | - |
| FR-STORAGE-0003 | storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl) | Fat32Driver: fstat(FileHandle) and readdir(DirHandle) via handle | - |
| FR-STORAGE-0004 | nvfs | MountTable.resolve() uses slice() which is broken in baremetal Cranelift | - |
| FR-STORAGE-E2E-001 | simple_db_+_nvfs_shim | End-to-end integration test: Simple DB WAL+pmap through NVFS shim | - |
| LZMA2_FULL_LCLPPB_2026_05_01 | lzma2 | LZMA2 — Full LC/LP/PB Property Support | - |
