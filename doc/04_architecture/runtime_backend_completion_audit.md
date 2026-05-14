# Runtime Backend Completion Audit

Updated: 2026-05-14

## Objective Restatement

Refactor the Simple runtime libraries so compatibility families depend on a no-GC async/no-GC backend where behavior allows it, keep sync/GC variants as facades when they do not need independent behavior, prevent SimpleOS lower layers from depending on POSIX compatibility modules, and document the production backend ownership model.

## Evidence Checklist

| Requirement | Current evidence | Status |
| --- | --- | --- |
| Repeatable backend-boundary audit exists | `scripts/audit/runtime_backend_boundaries.py` checks tracked async compatibility families for direct `extern fn rt_*` ownership, SimpleOS native lower layers for POSIX/libc imports, and portable library roots for forbidden POSIX/Linux imports outside explicit platform/compatibility paths. | Closed for static boundary gate |
| Async/GC exact-copy runtime hooks are not duplicated across families | Scan over `src/lib/gc_async_mut` and `src/lib/nogc_async_mut` reports `exact_duplicate_runtime_hook_count=0` for files that match `nogc_sync_mut` byte-for-byte and declare `extern fn rt_*`. | Closed for exact-copy class |
| GC compatibility surfaces use no-GC async when async behavior must be preserved | `gc_async_mut/io/buffer.spl`, `gc_async_mut/torch/ffi.spl`, and `gc_async_mut/svllm/nvfs_client/*` are facades over `nogc_async_mut` backends. The no-GC async Torch FFI now delegates to the no-GC sync Torch FFI because that FFI surface is synchronous backend ownership, not async behavior. | Partially closed |
| Async compatibility surfaces use shared no-GC backends when behavior is identical or import-drift only | Reviewed facade closures are recorded in `runtime_family_support_matrix.md`; targeted `simple check` passed for each changed facade slice. `gc_async_mut` and `nogc_async_mut` package FFI, platform helper roots, and SIMD roots now export the no-GC sync backend instead of redeclaring synchronous runtime hooks; family-specific mimalloc TLS adapters import thread-local hooks from a no-GC sync runtime owner while preserving each family's `MiHeap` types; browser session file reads now use the no-GC sync file-ops wrapper. | Partially closed |
| No-GC async files with no-GC sync counterparts do not redeclare backend hooks after review | The reviewed behavior-diff set (`torch/ffi`, `cuda/ffi`, `cuda/mod`, `gpu/memory`, `http_server/response`, `io/buffer`, `io/file`, `package_ffi`, `platform`, `simd`, `mimalloc_tls`, `coverage`, `atomic`, `conf`, `fuzz`) now has no local `extern fn rt_*` declarations. Remaining runtime hooks were moved to no-GC sync backend owners such as `cuda/ffi.spl`, `ptr/raw.spl`, `io/dir_entry_ops.spl`, and `runtime/thread_local.spl`, replaced with pure Simple conversion helpers, represented as facades over no-GC sync roots, or routed through no-GC sync file/dir wrappers for MCP and HTTP file helpers; HTTP server time helpers now use `nogc_sync_mut.io.time_ops.current_time_ms`, access logging uses `nogc_sync_mut.io.file_ops.file_append`, and HTTP compression text conversion is pure Simple. A tracked scan now finds no `nogc_async_mut` runtime-hook file with a same-path `nogc_sync_mut` counterpart. | Closed for same-path counterpart class |
| SimpleOS kernel/drivers/services/SOSIX/userlib/async do not depend on POSIX compatibility modules | `scripts/audit/runtime_backend_boundaries.py` reports `simpleos_lower_layer_posix_libc_import_count=0`. Shared FD/process/pipe/socket ownership lives under `src/os/kernel/`; `src/os/posix/` modules are facades. | Closed for scanned lower layers |
| Portable stdlib/library roots do not import POSIX/Linux modules except explicit platform/compatibility paths | `scripts/audit/runtime_backend_boundaries.py` reports `portable_lib_forbidden_posix_linux_import_count=0`, excluding paths named as POSIX/Linux/platform compatibility owners. | Closed for static import gate |
| Production architecture is documented | `runtime_family_support_matrix.md` records current facade closures, SimpleOS POSIX boundary, and remaining runtime-hook review items. | Partially closed |

## Latest Boundary Verification

Executed on 2026-05-14:

- `python3 scripts/audit/runtime_backend_boundaries.py`
  - `async_compat_direct_runtime_hook_count=0`
  - `simpleos_lower_layer_posix_libc_import_count=0`
  - `portable_lib_forbidden_posix_linux_import_count=0`
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/os/kernel src/os/drivers src/os/services src/os/sosix src/os/userlib src/os/async`
  - exit code `0`
  - `61 warning(s) found in 443 file(s)`, all observed warnings were unresolved `common`/`lib.common` imports from running this check over the OS roots without the full source-root closure.
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/lib`
  - exit code `0`
  - `3875` OK check markers, `1011` warnings, and `0` errors in `build/audit/full_src_lib_check.log`
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/os/posix src/os/libc`
  - exit code `0`
  - `17` OK check markers, `0` warnings, and `0` errors in `build/audit/simpleos_posix_libc_check.log`

## Remaining Gaps

| Gap | Evidence | Next action |
| --- | --- | --- |
| GC async still has GC-only runtime-hook files | Current tracked-only scan reports 0 GC async hook files / 0 hook declarations after package FFI, platform root, SIMD, mimalloc TLS hook-owner, browser-session file-read closure, CUDA GPU FFI facade closure, Vulkan compute/graphics FFI ownership move to `nogc_sync_mut.io.vulkan_ffi`, OpenGL/Metal/ROCm/oneAPI I/O FFI ownership moves to no-GC sync owners, 2D/3D GPU FFI dispatch ownership moves to no-GC sync, 2D/3D CUDA/Vulkan/ROCm/Intel FFI wrapper ownership moves to no-GC sync, shared 2D/3D SIMD/color/type helper ownership moves to no-GC sync, shared 3D backend math hook ownership move to `nogc_sync_mut.gpu.engine3d.math_hooks`, shared CPU presentation hook ownership move to `nogc_sync_mut.gpu.present_hooks`, Vulkan backend/helper dispatch routing to `nogc_sync_mut.gpu.engine2d.ffi_vulkan`, Metal backend/helper dispatch routing to `nogc_sync_mut.io.metal_ffi`, WebGPU backend hook ownership move to `nogc_sync_mut.gpu.engine2d.webgpu_ffi`, framebuffer blit hook ownership move to `nogc_sync_mut.gpu.engine2d.framebuffer_hooks`, CUDA/ROCm/Intel 2D engine helper hook routing through no-GC sync engine FFI owners, CUDA I/O legacy ABI ownership move to `nogc_sync_mut.io.cuda_ffi`, and removal of a comment-only `extern fn rt_cuda_*` scan false positive in `gc_async_mut/gpu.spl`. | Maintain this scan at zero; new GC async runtime hooks require a documented backend-owner exception. |
| No-GC async still has runtime-hook files without sync counterparts | Current tracked-only scan reports 0 no-GC async hook files / 0 hook declarations. MCP entrypoint GC collection cadence now calls the no-GC sync runtime wrapper instead of owning local GC hooks, DNS resolver packet text conversion now uses pure text byte helpers, async byte file operations use the no-GC sync FFI byte-file owner, the SVLLM std-fs adapter imports the same file owner for byte writes/existence checks/atomic publish rename, LLM HTTP providers import the no-GC sync HTTP FFI raw request wrapper, LLM diagnostics hook stdin reads use the no-GC sync pipe reader, LLM diagnostics WebSocket export sends through the no-GC sync HTTP/WebSocket FFI owner, the top-level no-GC async concurrency aggregate now reuses the channel/thread modules and no-GC sync atomic wrappers instead of redeclaring those runtime hooks, no-GC async channel/thread/mutex/RwLock modules are facades over no-GC sync concurrency backend owners, async SFFI now documents its pure Simple ownership without commented runtime-hook examples, TLS I/O/hex helpers reuse the TLS common byte encoder, TLS stream hex crypto calls route through TLS common hex-domain wrappers, TLS handshake crypto calls route through TLS common crypto wrappers, actor runtime hooks route through `nogc_sync_mut.concurrent.actor_hooks`, TLS common crypto/wire hooks route through `nogc_sync_mut.io.tls_common_hooks`, and WebSocket raw async frame I/O routes through `nogc_sync_mut.websocket.async_wire_hooks`. | Maintain this scan at zero; new no-GC async runtime hooks require a documented async-specific backend-owner exception. |
| Runtime/native execution coverage has not run | Broad static checks now pass for `src/lib`, SimpleOS native lower layers, and SimpleOS POSIX/libc wrappers, but no runtime/native actor, TLS, WebSocket, GPU, CUDA, or OS boot execution suites were run. | Add or run representative runtime/native execution tests for the backend-owner paths before declaring production completion. |
| Sync-backed-by-async policy is not globally proven | The current architecture still uses `nogc_sync_mut` as the canonical backend for many compatibility facades where async behavior is not required. | Decide whether this is accepted backend policy or migrate selected sync surfaces onto blocking wrappers over `nogc_async_mut`. |
