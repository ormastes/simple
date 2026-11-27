# Full CLI native link: 5 Simple symbols with no implementation

Status: verification-pending
Date: 2026-11-15

## Symptom
`native-build src/app/cli/main.spl` with the phase-1 seed compiled every
module (`compiled=5 reused=3141 failed=0`) and then refused the link:
`5 internal Simple symbol(s) have no implementation ...: _now_ms,
file_metadata, spl_fonts_call_init_blob, spl_fonts_call_init_path,
spl_fonts_call_layout_text`. The hosted lane links the C core runtime
(`core_c_runtime/simple_runtime.lib`), not the Rust runtime.

## Root causes
1. `_now_ms` (`src/os/_QemuRunner/os_build_run.spl:219`): the function is
   `pub fn _now_ms` in `runner_targets.spl`, imported only through
   `use os._QemuRunner.runner_targets.*`. The glob import resolves it for
   type-checking but native codegen emits the bare name `_now_ms` instead of
   `os___QemuRunner__runner_targets___now_ms` (glob import of an
   underscore-prefixed name is a resolver/codegen gap). Fixed locally with an
   explicit `use ...runner_targets.{_now_ms}`; the glob gap itself remains open.
2. `file_metadata` (`std.nogc_{sync,async}_mut.fs.flat`): a bare
   `extern fn file_metadata` with no runtime symbol in either runtime
   (interpreter: `unknown extern function: file_metadata`). Replaced by a
   pure-Simple composition of `dir_exists`/`file_exists`/`file_size`/
   `file_is_regular_no_follow`/`file_modified_time`.
   **Remaining gap:** `is_symlink`, `readonly`, `created` are not observable
   through any C-runtime scalar probe and are reported `false/false/0`.
3. `spl_fonts_call_*`: implemented only in the Rust runtime
   (`wsffi_native.rs`); the C runtime had no twin. Added C twins in
   `src/runtime/runtime_native.c` with the same (ptr,len) contract.

## Evidence
Regression spec: `test/01_unit/lib/nogc_sync_mut/fs/flat_file_metadata_spec.spl`
(RED: `semantic: unknown extern function: file_metadata`; GREEN: 1 passed).

## Native CLI smoke (phase-1 seed, K1 `llvm` composition)
Build: `native-build --source src/compositions/kernel_llvm --source src/compositions/cuda_disabled --source src/compiler --source src/app --source src/lib --source src/plugins --entry-closure src/app/cli/main.spl`
-> `Build complete: 3153 compiled, 0 cached, 0 failed`, 84027 KB, 415 abort-stubs.
sha256 `7f9c35460ecc4deb39ba43a3cc76c81de87573d52b6b41032183a38a0b14bf40`.
(Without the K1 composition every command fails closed with `PLUG-E-K1-POLICY`.)
- `--version` -> rc=0, `Simple v1.0.0-rc.1`.
- `test <spec>` -> rc=1, `SCV-E-ADMISSION: snapshot-read-failed:test/cert/tool_qual/meta/deterministic/01_arithmetic.spl`
  (that path is a git symlink -> `../../positive/01_arithmetic.spl`; the native
  SCV snapshot reader (`src/lib/scv/compile_snapshot.spl`) refuses it, while the
  seed interpreter runs the same spec GREEN). **Open**, next gap for the native CLI.

## Addendum: `CompareObjectHandles` unresolved (release tip, f2c15a69f33)
`windows_service_logon_namespace_abi_v1.spl` declared `CompareObjectHandles`
as a direct extern; llvm-mingw's kernel32/kernelbase/advapi32/ntdll import
libs do not export it (only libmincore/libonecore), and the seed link list does
not add those. Fix: `rt_win_compare_object_handles` in `runtime_native.c`
(core-C member) resolves it via `GetProcAddress(GetModuleHandleW(L"kernelbase.dll"))`,
returns 0 (not identical, fail closed) when unavailable or off Windows.
Result: full CLI links (`Build complete: 3713 units, 0 failed`), `--version` rc=0.
**Not covered / open:** (1) Rust seed interpreter twin of the extern is not
registered (no seed rebuild in this lane), so the interpreted spec
`test/01_unit/lib/io/windows_compare_object_handles_spec.spl` stays red under the
seed; (2) the native CLI's `test` command fails every spec with
`function 'describe' not found` (std.spec not resolved in the native interpreter).
Status: verification-pending.

Update 2026-11-16: `rt_win_compare_object_handles` needs no separate codegen
table entry. Other `rt_win_*` externs are not listed in `runtime_sffi.rs` either;
a native-built probe resolves the symbol from the C runtime and links with no
stub. Pinned by `test/03_system/runtime/win_compare_object_handles_native_spec.spl`
(same handle -> true, different -> false). Interpreter twin landed in #9664.

## Update 2026-11-16: stubbed-symbol census of the tip full-CLI build

Build: release tip c0fecc6e751, seed `seed-20261117/simple.exe`, K1 `llvm` composition,
`Build complete: 4 compiled, 3869 cached, 0 failed`, `cli_tip.exe` 99412 KB, 403 abort-stubbed
symbols (`cli_tip.exe.stubbed_symbols.txt`; `rt_tls_*` excluded from this lane).
Classification = C definition lookup under `src/runtime/**` (non-vendor) against the
`runtime_inputs` list in `native_project/tools.rs`, then Rust-runtime lookup for the rest.

| Category | Count | Families | Cause / action |
|---|---|---|---|
| 1. C file exists, not in Windows archive list | 15 | `rt_db_*` (`runtime_db.c`, self-contained, sole definer) | **Fixed here**: `runtime_db.c` added to the core-C list. |
| 1b. C file exists, not in list, deliberately | 25 | `rt_vulkan_async_session_*`, `rt_metal_*`, `rt_cuda_launch_kernel_ex` (`runtime_dynload.c`) | NOT added: 12 of its exported symbols are also defined in `runtime_native.c` (duplicate-definition link error). Needs an owner split of the GPU-provider loader. |
| 1c. Optional-SDK C files | 74 + 31 + 2 | `rt_sdl2_*`/`rt_sdl_*` (`runtime_sdl2.c`), `rt_rocm_*`/`rt_engine2d_rocm_*` (`runtime_rocm.c`), `rt_cuda_memcpy_*` (`scilib/cublas_shim.c`) | Need SDL2/ROCm/cuBLAS provider libs (dlopen'd providers in their own libs); not archive-list gaps. |
| 1d. Wrong lane | 18 | `rt_port_*`, `rt_hlt/sti/lgdt/lidt/ltr/read_msr/write_msr/read_cr2/mmio_write_u64`, `rt_cli` (`startup/baremetal/*`), `rt_browser_http_job_free` (`test/*selfcheck.c`) | Baremetal/selfcheck sources, must not be in a hosted archive. Dead externs on the hosted CLI. |
| 2. C owner excluded from list | 3 | `rt_set_debug_mode`, `rt_set_macro_trace`, `rt_is_macro_trace_enabled` (`runtime.c`, only used as root probe at tools.rs:476) | Rust-only in the core lane; needs a C twin in `runtime_native.c`. |
| 2b. Non-target hosted stubs (fail closed by design) | 22 | `rt_cocoa_*` (12), `rt_win32_dib_*`/`rt_win32_window_*` (10) | `hosted_cocoa.c`/`hosted_win32.c` are in the list but compiled to fail-closed stubs on this target. Expected. |
| 3. No C definition anywhere (Rust-only or dead) | 213 | `rt_vulkan_*` 66, `rt_cuda_*` 36, `rt_metal_*` 34, `rt_winit_*` 10, `rt_oneapi_*` 10, `rt_intel_*` 10, `rt_mmio_*_real` 5, `rt_engine2d_*` 5, `rt_webgpu` 3, `rt_virtio/virtq` 5, `rt_profiler_*` 3, `rt_term_*` 2, `rt_mem_*_boxed` 2, `rt_ghdl_*` 2, plus singletons (`rt_alloc_page_aligned`, `rt_cli_run_tests`, `rt_cpu_arch_name`, `rt_current_time_ms`, `rt_font_load_array`, `rt_gui_blend_span8`, `rt_madvise_raw`, `rt_mlock`, `rt_munlock`, `rt_msync_flags`, `rt_x86_syscall`, `rt_tls13_aes128_gcm_decrypt`, ...) | GPU backends live in the Rust runtime (`vulkan_graphics_runtime_*.rs`, `metal_graphics_runtime.rs`, `cuda_runtime.rs`); the rest are either Rust-only needing a C twin (`rt_mlock`, `rt_munlock`, `rt_msync_flags`, `rt_madvise_raw`, `rt_profiler_*`, `rt_term_*`, `rt_current_time_ms`, `rt_alloc_page_aligned`) or dead declarations. Per-symbol split is a follow-up; the full list is in the lane scratchpad (`full_cli_tip_stubbed_symbols_20261116.txt`).

Counts: 15 + 25 + 107 + 18 + 3 + 22 + 213 = 403 (matches the stub file).
### Native CLI smoke on tip (local build)
`cli_tip.exe test` on `array_at_option_spec`, `array_get_option_spec`,
`nogc_sync_mut/fs/host_path_spec`: each `rc=1`, `Results: 1 total, 0 passed, 1 failed`
(`Process exited with code 1` from the child after ~99 s; no spec-level message surfaced).
The native CLI `test` command is still not green. Open.

### Local-only workarounds needed to build the tip with seed-20261117 (NOT committed)
The tip failed HIR lowering under this seed: `trace_query_error_v1` 4th default arg
(`query_main.spl`, `query_cmds_main_v1.spl`), `disk_admission_decide_present` (`free.value` on a
`unit` type), `gui_render_lsp_navigation_tools_html` (`struct 'ANY' field 'path'`).
`simple_web_html_layout_renderer.spl` needs `native-build --timeout 1200` (300 s default is
too short, never cached).

Status: verification-pending (category 1 fix not link-verified: needs a seed rebuild).
