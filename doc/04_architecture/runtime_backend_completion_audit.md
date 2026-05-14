# Runtime Backend Completion Audit

Updated: 2026-05-14

## Objective Restatement

Refactor the Simple runtime libraries so compatibility families depend on a no-GC async/no-GC backend where behavior allows it, keep sync/GC variants as facades when they do not need independent behavior, prevent SimpleOS lower layers from depending on POSIX compatibility modules, and document the production backend ownership model.

## Evidence Checklist

| Requirement | Current evidence | Status |
| --- | --- | --- |
| Repeatable backend-boundary audit exists | `scripts/audit/runtime_backend_boundaries.py` checks tracked async compatibility families for direct `extern fn rt_*` ownership, no-GC async wildcard facades over no-GC sync runtime-hook owners, SimpleOS native lower layers for POSIX/libc imports, and portable library roots for forbidden POSIX/Linux imports outside explicit platform/compatibility paths. | Closed for static boundary gate |
| Async/GC exact-copy runtime hooks are not duplicated across families | Scan over `src/lib/gc_async_mut` and `src/lib/nogc_async_mut` reports `exact_duplicate_runtime_hook_count=0` for files that match `nogc_sync_mut` byte-for-byte and declare `extern fn rt_*`. | Closed for exact-copy class |
| GC compatibility surfaces use no-GC async when async behavior must be preserved | `gc_async_mut/io/buffer.spl`, `gc_async_mut/torch/ffi.spl`, `gc_async_mut/svllm/nvfs_client/*`, and `gc_async_mut/db/*` are facades over `nogc_async_mut` backends. The no-GC async Torch FFI delegates to the no-GC sync Torch FFI because that FFI surface is synchronous backend ownership, not async behavior. The routing policy in `runtime_family_support_matrix.md` makes this explicit. | Closed for documented routing policy and static facade gate |
| Async compatibility surfaces use shared no-GC backends when behavior is identical or import-drift only | Reviewed facade closures are recorded in `runtime_family_support_matrix.md`; targeted `simple check` passed for each changed facade slice. `gc_async_mut` and `nogc_async_mut` package FFI, platform helper roots, and SIMD roots now export the no-GC sync backend instead of redeclaring synchronous runtime hooks; no-GC async top-level atomic, cache operation/helper, DMA, volatile ops, SIMD, SQLite FFI, database atomic/core/checker/requirement/todo, desktop dialog/display/global_shortcut/lifecycle/notification/power/protocol/shell_open/tray/updater, I/O debug_state/debug_stubs/file_discovery/file_shell/signal_handlers, serial_proxy/time_ops/ssh_serial, profiler_simple, sysinfo_ops, thread helpers, env_ops, VHDL FFI, DH FFI, dir_ops, signal stubs, shell env, test-runner resource/classification/args/async/files/system_monitor/coverage/manifest_scanner, security audit_chain/audit_log/types, LSP lsp_query/parser_adapter/diagnostics/main_wasi/handlers/main, MCDC, log, package dist, experiment artifact/config/sweep, OIDC discovery/id_token, spec decorators/env_detect, hooks mod/stop, FFI dynamic/dynamic_versioned, benchmark string_bench, gpu_runtime/mod, platform root/linker, play expect/electron_application/page/sdl2_backend/wm/xvfb, terminal credential config, daemon SDK types/runner/client, dSYM resolver, OpenOCD protocol, FFI coverage, coverage/fuzz helpers, JS interpreter core, debug remote ST-Link/T32-window/QEMU runner, shader_compile, pipe, config, debug remote DWARF/ptrace, process-limit, LSP protocol, mem-tracker, and test-runner process/lifecycle/parsing facades now use explicit public exports over no-GC sync owners instead of wildcard facades; `ffi/mod` no longer wildcard-exports the documentation-only sync root. The runtime-hook owner wildcard scan now reports `remaining=0`. Family-specific mimalloc TLS adapters import thread-local hooks from a no-GC sync runtime owner while preserving each family's `MiHeap` types; browser session file reads now use the no-GC sync file-ops wrapper. | Closed for reviewed wildcard facade class |
| No-GC async files with no-GC sync counterparts do not redeclare backend hooks after review | The reviewed behavior-diff set (`torch/ffi`, `cuda/ffi`, `cuda/mod`, `gpu/memory`, `http_server/response`, `io/buffer`, `io/file`, `package_ffi`, `platform`, `simd`, `mimalloc_tls`, `coverage`, `atomic`, `conf`, `fuzz`) now has no local `extern fn rt_*` declarations. Remaining runtime hooks were moved to no-GC sync backend owners such as `cuda/ffi.spl`, `ptr/raw.spl`, `io/dir_entry_ops.spl`, and `runtime/thread_local.spl`, replaced with pure Simple conversion helpers, represented as facades over no-GC sync roots, or routed through no-GC sync file/dir wrappers for MCP and HTTP file helpers; HTTP server time helpers now use `nogc_sync_mut.io.time_ops.current_time_ms`, access logging uses `nogc_sync_mut.io.file_ops.file_append`, and HTTP compression text conversion is pure Simple. A tracked scan now finds no `nogc_async_mut` runtime-hook file with a same-path `nogc_sync_mut` counterpart. | Closed for same-path counterpart class |
| SimpleOS kernel/drivers/services/SOSIX/userlib/async do not depend on POSIX compatibility modules | `scripts/audit/runtime_backend_boundaries.py` reports `simpleos_lower_layer_posix_libc_import_count=0`. Shared FD/process/pipe/socket ownership lives under `src/os/kernel/`; `src/os/posix/` modules are facades. | Closed for scanned lower layers |
| Portable stdlib/library roots do not import POSIX/Linux modules except explicit platform/compatibility paths | `scripts/audit/runtime_backend_boundaries.py` reports `portable_lib_forbidden_posix_linux_import_count=0`, excluding paths named as POSIX/Linux/platform compatibility owners. | Closed for static import gate |
| Production architecture is documented | `runtime_family_support_matrix.md` records current family counts, loader order, facade closures, backend routing policy, SimpleOS POSIX boundary, and remaining promotion gaps. | Closed for current architecture contract |
| GC async one-line facades do not self-reexport when no-GC async owners exist | A precise scan for tracked one-line `export use (std.)?gc_async_mut.*` files, including top-level `src/lib/gc_async_mut/*.spl`, now reports `0` remaining after TLS, TCP, WebSocket, web-framework, hooks/detectors, HTTP/3, MCP SDK server/transport, play/CDP, sanitizer, security, storage, replay, `src` compatibility, terminal, web UI, TUI, STOMP, text layout, UI test, SPostgre IF, unsafe, test, testing, UI, tmux, test-runner, timing, and UDP utility closures. | Closed for tracked one-line self-facade class |
| GC async runtime-owner wildcard facades route through no-GC async where possible | `scripts/audit/runtime_backend_boundaries.py` now reports `gc_async_runtime_owner_wildcard_facade_count=0`. GC async compatibility facades with matching no-GC async surfaces now export those no-GC async facades first; the remaining GPU and device FFI API-shape gaps were closed by adding no-GC async facades over the no-GC sync backend owners. | Closed for tracked runtime-owner wildcard facade class |
| Sync/GC and sync/immutable family names exist as backend-backed compatibility surfaces | `src/lib/gc_sync_mut`, `src/lib/gc_async_immut`, `src/lib/gc_sync_immut`, and `src/lib/nogc_sync_immut` now exist as facade-only compatibility families. `gc_sync_mut` exports tracked `gc_async_mut` modules; immutable variants export `nogc_async_immut` / `gc_async_immut` surfaces. Interpreter fallback search and family extraction recognize all four names. | Advanced-scoped; broader runtime coverage still needed |
| New facade-only runtime families have focused import and behavior coverage | `test/unit/lib/{gc_sync_mut,gc_async_immut,gc_sync_immut,nogc_sync_immut}/facade_resolution_spec.spl` each pass in interpreter mode. The specs exercise representative pure helpers, immutable functional helpers, and root coordination types through the facade family names. `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` facade resolution specs now pass in native mode after routing public immutable array combinators through builtin `len(...)` dispatch, with focused native probes covering root `Atom`, `VersionedSnapshot`, and root pmap/version access. | Closed for focused interpreter and native facade behavior coverage |

## Latest Boundary Verification

Executed on 2026-05-14:

- `python3 scripts/audit/runtime_backend_boundaries.py`
  - `async_compat_direct_runtime_hook_count=0`
  - `gc_async_runtime_owner_wildcard_facade_count=0`
  - `nogc_async_runtime_owner_wildcard_facade_count=0`
  - `simpleos_lower_layer_posix_libc_import_count=0`
  - `portable_lib_forbidden_posix_linux_import_count=0`
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check $(cat /tmp/simple_backend_slice_spl_files.txt)`
  - exit code `0`
  - `122` changed Simple facade files checked, `0` errors
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/lib/gc_sync_mut src/lib/gc_async_immut src/lib/gc_sync_immut src/lib/nogc_sync_immut src/compiler/10.frontend/core/interpreter/module_loader.spl src/compiler/35.semantics/gc_boundary_check.spl`
  - exit code `0`
  - `880` generated facade/compiler files checked, `0` errors
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/lib/{gc_sync_mut,gc_async_immut,gc_sync_immut,nogc_sync_immut}/facade_resolution_spec.spl --mode=interpreter --clean --force-rebuild` (run as four focused commands)
  - `8` examples passed, `0` failures
  - non-fatal `export use *` warnings remain on generated compatibility facades even with `@allow(star_import)` reasons
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/lib/gc_sync_mut/facade_resolution_spec.spl --mode=native --clean --force-rebuild`
  - exit code `0`
  - `1` native spec file passed in `4144ms`
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_immut/facade_resolution_spec.spl --mode=native --clean --force-rebuild`
  - exit code `0`
  - `1` native spec file passed in about `9s`
  - root facade imports now keep plain-array combinators on native builtin `len(...)` dispatch instead of resolving array length through persistent-list methods
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_immut/{atom_native_probe_spec.spl,versioned_native_probe_spec.spl,root_version_native_probe_spec.spl,root_pmap_native_probe_spec.spl,root_native_probe_spec.spl,native_combinators_spec.spl} --mode=native --clean --force-rebuild` (run as focused one-file commands)
  - exit code `0` across the focused loop
  - probes cover direct and root-facade `Atom`, direct and root-facade `VersionedSnapshot`, root pmap traversal, and immutable combinator chains
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_sync_immut/facade_resolution_spec.spl --mode=native --clean --force-rebuild`
  - exit code `0`
  - `1` native spec file passed
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/nogc_sync_immut/facade_resolution_spec.spl --mode=native --clean --force-rebuild`
  - exit code `0`
  - `1` native spec file passed
  - non-fatal native warnings remain for empty-module type loading and minimal-runtime atomic stubs; the hosted runtime bundle can provide real `rt_atomic_*` symbols
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/persistent_collections_native_spec.spl --mode=native --clean --force-rebuild` (run as three focused commands)
  - exit code `0` for all three focused native runs
  - validates root-facade `PersistentList` structural sharing through the GC async, GC sync immutable, and no-GC sync immutable compatibility families
  - `PersistentList` now uses explicit returns on exercised public methods; internal no-GC immutable array length calls use builtin `len(...)` so root facade imports cannot redirect plain-array length dispatch
- `SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_immut/{vector_empty_native_probe_spec.spl,vector_push_empty_native_probe_spec.spl} --mode=native --clean --force-rebuild` (run as focused one-file commands)
  - exit code `0` for both focused native runs
  - validates root-facade `PersistentVec.empty()` and a single tail-only `push()` through the GC async immutable facade
  - multi-push / `from_array` vector probes still fail natively, so vector remains below promotion threshold
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/native_combinators_spec.spl --mode=interpreter/native --clean --force-rebuild` (run as three files, both modes)
  - `3` interpreter spec files passed, `0` failures
  - `3` native spec files passed, `0` failures
  - validates pure immutable combinator facade chains without the Atom runtime dependency
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/os/kernel src/os/drivers src/os/services src/os/sosix src/os/userlib src/os/async`
  - exit code `0`
  - `61 warning(s) found in 443 file(s)`, all observed warnings were unresolved `common`/`lib.common` imports from running this check over the OS roots without the full source-root closure.
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/lib`
  - exit code `0`
  - `3875` OK check markers, `1011` warnings, and `0` errors in `build/audit/full_src_lib_check.log`
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/os/posix src/os/libc`
  - exit code `0`
  - `17` OK check markers, `0` warnings, and `0` errors in `build/audit/simpleos_posix_libc_check.log`
- `python3 scripts/audit/runtime_backend_boundaries.py`
  - final focused rerun reports `"pass": true`
- No-GC async wildcard facade review scan:
  - Historical step-down scans are superseded by the final closure result below; current audit evidence is `remaining=0`.
- No-GC async final runtime-owner wildcard facade review scan:
  - `remaining=0` after narrowing `io/pipe`, `conf`, debug remote DWARF/ptrace, `ffi/mod`, `io/process_limit_enforcer`, `lsp/lsp_protocol`, `mem_tracker/mod`, and test-runner process/lifecycle/parsing facades.
- Focused runtime-path specs:
  - `test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `5` passed, `0` failed
  - `test/unit/lib/gc_async_mut/tls/tls_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `5` passed, `0` failed
  - `test/unit/lib/gc_async_mut/tcp/tcp_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/actor_dispatch_spec.spl --mode=interpreter --clean --force-rebuild`: `11` passed, `0` failed
  - `test/unit/lib/gc_async_mut/websocket/websocket_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/web_framework/web_framework_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/gc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/gc_async_mut/mcp_sdk/transport/mcp_sdk_transport_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/http/h3/http_h3_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/mcp_sdk/transport/mcp_sdk_transport_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/play/cdp/play_cdp_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/play/cdp/play_cdp_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/gc_async_mut/sanitizer/{asan,lsan,msan,tsan,ubsan}/*_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `8` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/sanitizer/{asan,lsan,msan,tsan,ubsan}/*_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `8` passed, `0` failed
  - `test/unit/lib/gc_async_mut/security/{aspects,enforcement,validation}/*_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `4` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/security/{aspects,enforcement,validation}/*_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `4` passed, `0` failed
  - `test/unit/lib/gc_async_mut/storage/{storage_init,storage_policy}_facade_spec.spl` and `storage/shared/storage_shared_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `4` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/storage/{storage_init,storage_policy}_facade_spec.spl` and `storage/shared/storage_shared_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `4` passed, `0` failed
  - `test/unit/lib/gc_async_mut/replay/**/*_facade_spec.spl --mode=interpreter --force`: `21` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/replay/**/*_facade_spec.spl --mode=interpreter --force`: `20` passed, `0` failed
  - `test/unit/lib/gc_async_mut/src/{app,collections,core,dl,math,tensor,tooling}/*_facade_spec.spl` plus `src_time_facade_spec.spl --mode=interpreter --force`: `10` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/src/{app,collections,core,dl,math,tensor,tooling}/*_facade_spec.spl` plus `src_time_facade_spec.spl --mode=interpreter --force`: `10` passed, `0` failed
  - `test/unit/lib/gc_async_mut/terminal/{terminal_types_facade_spec,credential/terminal_credential_facade_spec,power/terminal_power_facade_spec}.spl --mode=interpreter --force`: `3` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/terminal/{terminal_types_facade_spec,credential/terminal_credential_facade_spec,power/terminal_power_facade_spec}.spl --mode=interpreter --force`: `3` passed, `0` failed
  - `test/unit/lib/gc_async_mut/web_ui/web_ui_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/tui/{tui_facade_spec,widgets/tui_widgets_facade_spec}.spl --mode=interpreter --force`: `2` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/tui/{tui_facade_spec,widgets/tui_widgets_facade_spec}.spl --mode=interpreter --force`: `2` passed, `0` failed
  - `test/unit/lib/gc_async_mut/stomp/stomp_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/stomp/stomp_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/text_layout/text_layout_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/ui_test/ui_test_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/ui_test/ui_test_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/spostgre_if/spostgre_if_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/spostgre_if/spostgre_if_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/unsafe/unsafe_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/unsafe/unsafe_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/testing/testing_attributes_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/testing/testing_attributes_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/ui/ui_platform_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/ui/ui_platform_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/tmux/tmux_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/tmux/tmux_facade_spec.spl --mode=interpreter --force`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/test_runner/test_stats_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `3` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `3` passed, `0` failed
  - `test/unit/lib/gc_async_mut/timing_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/timing_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/udp_utils_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/udp_utils_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `1` passed, `0` failed
  - `test/unit/lib/gc_async_mut/db/{db_accel_facade_spec,db_init_facade_spec}.spl`, `test/unit/lib/gc_async_mut/db/dbfs_driver/*_facade_spec.spl`, and `test/unit/lib/gc_async_mut/db/dbfs_engine/{dbfs_engine_facade_spec,dbfs_backend_facade_spec,dbfs_meta_store_facade_spec,dbfs_schema_facade_spec,dbfs_recovery_namespace_facade_spec,dbfs_checkpoint_attr_facade_spec,arena_parity_spec}.spl --mode=interpreter --clean --force-rebuild`: `14` passed, `0` failed
  - `test/unit/lib/nogc_async_mut/db/dbfs_driver/*_facade_spec.spl --mode=interpreter --clean --force-rebuild`: `2` passed, `0` failed
  - `test/unit/lib/gpu/engine2d/ffi_dispatch_spec.spl --mode=interpreter --clean --force-rebuild`: `7` passed, `0` failed
  - `test/unit/lib/gpu/engine2d/ffi_cuda_spec.spl --mode=interpreter --clean --force-rebuild`: `11` passed, `0` failed
  - `cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl --mode=interpreter --clean --force-rebuild`: `4` passed, `0` failed
  - `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-common -p simple-compiler`: exit code `0`
- Required smoke gates:
  - `sh scripts/check-core-runtime-smoke.shs src/compiler_rust/target/bootstrap/simple`: `core_runtime_smoke=true`
  - `SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple MCP_SERVER=build/bootstrap/mcp-package/simple_mcp_server LSP_MCP_SERVER=build/bootstrap/mcp-package/simple_lsp_mcp_server sh scripts/check-mcp-native-smoke.shs`: JSON/schema validation passed for both servers

## Remaining Gaps

| Gap | Evidence | Next action |
| --- | --- | --- |
| GC async still has GC-only runtime-hook files | Current tracked-only scan reports 0 GC async hook files / 0 hook declarations after package FFI, platform root, SIMD, mimalloc TLS hook-owner, browser-session file-read closure, CUDA GPU FFI facade closure, Vulkan compute/graphics FFI ownership move to `nogc_sync_mut.io.vulkan_ffi`, OpenGL/Metal/ROCm/oneAPI I/O FFI ownership moves to no-GC sync owners, 2D/3D GPU FFI dispatch ownership moves to no-GC sync, 2D/3D CUDA/Vulkan/ROCm/Intel FFI wrapper ownership moves to no-GC sync, shared 2D/3D SIMD/color/type helper ownership moves to no-GC sync, shared 3D backend math hook ownership move to `nogc_sync_mut.gpu.engine3d.math_hooks`, shared CPU presentation hook ownership move to `nogc_sync_mut.gpu.present_hooks`, Vulkan backend/helper dispatch routing to `nogc_sync_mut.gpu.engine2d.ffi_vulkan`, Metal backend/helper dispatch routing to `nogc_sync_mut.io.metal_ffi`, WebGPU backend hook ownership move to `nogc_sync_mut.gpu.engine2d.webgpu_ffi`, framebuffer blit hook ownership move to `nogc_sync_mut.gpu.engine2d.framebuffer_hooks`, CUDA/ROCm/Intel 2D engine helper hook routing through no-GC sync engine FFI owners, CUDA I/O legacy ABI ownership move to `nogc_sync_mut.io.cuda_ffi`, and removal of a comment-only `extern fn rt_cuda_*` scan false positive in `gc_async_mut/gpu.spl`. | Maintain this scan at zero; new GC async runtime hooks require a documented backend-owner exception. |
| No-GC async still has runtime-hook files without sync counterparts | Current tracked-only scan reports 0 no-GC async hook files / 0 hook declarations. MCP entrypoint GC collection cadence now calls the no-GC sync runtime wrapper instead of owning local GC hooks, DNS resolver packet text conversion now uses pure text byte helpers, async byte file operations use the no-GC sync FFI byte-file owner, the SVLLM std-fs adapter imports the same file owner for byte writes/existence checks/atomic publish rename, LLM HTTP providers import the no-GC sync HTTP FFI raw request wrapper, LLM diagnostics hook stdin reads use the no-GC sync pipe reader, LLM diagnostics WebSocket export sends through the no-GC sync HTTP/WebSocket FFI owner, the top-level no-GC async concurrency aggregate now reuses the channel/thread modules and no-GC sync atomic wrappers instead of redeclaring those runtime hooks, no-GC async channel/thread/mutex/RwLock modules are facades over no-GC sync concurrency backend owners, async SFFI now documents its pure Simple ownership without commented runtime-hook examples, TLS I/O/hex helpers reuse the TLS common byte encoder, TLS stream hex crypto calls route through TLS common hex-domain wrappers, TLS handshake crypto calls route through TLS common crypto wrappers, actor runtime hooks route through `nogc_sync_mut.concurrent.actor_hooks`, TLS common crypto/wire hooks route through `nogc_sync_mut.io.tls_common_hooks`, and WebSocket raw async frame I/O routes through `nogc_sync_mut.websocket.async_wire_hooks`. | Maintain this scan at zero; new no-GC async runtime hooks require a documented async-specific backend-owner exception. |
| Runtime/native execution coverage is still incomplete | Representative actor, TLS, WebSocket, web-framework facade, CUDA/engine FFI dispatch, and WebGPU interpreter specs now pass. No real hardware/native CUDA execution or OS boot execution suite was run. | Run hardware/native CUDA coverage where available and an OS boot suite before declaring production completion. |
| Sync-backed-by-async policy is accepted but not fully behavior-promoted | The architecture now documents a behavioral routing policy: async-visible APIs use `nogc_async_mut`; sync-only FFI ownership stays in `nogc_sync_mut`; `gc_sync_mut` remains a facade over `gc_async_mut` until APIs prove they need real blocking wrappers. | Add per-API blocking-wrapper behavior only where tests show facade export is insufficient. |
| New facade-only runtime families need broader runtime coverage before public promotion | `gc_sync_mut`, `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` now have source facades, interpreter recognition, focused interpreter behavior specs, native immutable facade resolution coverage, focused native probes for root immutable coordination/versioned containers, native root-facade `PersistentList` structural-sharing coverage for the immutable facade families, and partial `PersistentVec` native smoke coverage for empty/single-push GC async facade behavior. | Fix native multi-push / `from_array` vector behavior, add broader compiled suites for map/set/trie paths, and resolve remaining native type-loader/minimal-runtime-stub warnings before promoting them from advanced-scoped to public. |
| GC async one-line self-facade audit is closed for tracked files | A precise tracked scan reports 0 one-line `export use (std.)?gc_async_mut.*` files after including both nested modules and top-level `gc_async_mut` files. The broader backend policy still requires ongoing review for new compatibility modules and for non-one-line GC-specific implementations. | Maintain the scan at zero; new self-facade exceptions require explicit architecture documentation. |
