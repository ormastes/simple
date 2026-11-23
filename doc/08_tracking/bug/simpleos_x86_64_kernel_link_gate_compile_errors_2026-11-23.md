# SimpleOS x86_64 kernel link gate: compile errors fixed (926/926 compile), 52 undefined symbols at link (2026-11-23)

Gate: `scripts/check/check-simpleos-x86_64-kernel-link.shs --link-only`
(seed native-build, LLVM backend, `SIMPLE_NO_STUB_FALLBACK=1`, `--entry-closure`,
entry `examples/09_embedded/simple_os/arch/x86_64/os_entry.spl`).
Seed tested: `/tmp/xc-llvm-seed-target/release/simple` (LLVM 23.1.1 seed).

Latest verdict (`OUT=/tmp/xc-out-x64-link`, real x86_64 boot C runtime linked without
`SIMPLE_BOOT_MINIMAL=1`):
`FAIL - 52 undefined symbol(s)` (`exit 1`), `[native-build] compiled=4 reused=922 failed=0`
(after initial full clean compile `[native-build] compiled=926 reused=0 failed=0`).
Earlier run with `SIMPLE_BOOT_MINIMAL=1` (excluding `rt_extras.c`/`primitives.c`/
`freestanding_*`) also compiled all 926 files (`failed=0`) and reported
`FAIL - 303 undefined symbol(s)`, of which 249 are already defined in the real
x86_64 boot C runtime files (`rt_extras.c`, `primitives.c`, `collections.c`,
`hashmap.c`, `freestanding_optional_backends.c`, `freestanding_value_registry.c`,
`baremetal_boot_stdout.c`, `runtime_service_owners.c`, `glass_render.c`).

## Fixed compile & gate defects (2026-11-23)

1. `scripts/check/check-simpleos-x86_64-kernel-link.shs`: added throwaway Ed25519
   key generation + `$OUT/generated/x86_64_auth_trust_config.spl` (`--source "$GEN"`)
   matching `check-simpleos-riscv64-user-elf-opensbi.shs`, resolving the missing
   `x86_64_auth_trust_config` imports in `x86_64_simplebox_catalog_media_boot_v1.spl`,
   `x86_64_authenticated_media_fixture.spl`, `x86_64_scr2_native_catalog_policy_v1.spl`,
   and `x86_64_signed_artifact_receipt_boot_policy_v2.spl`. Also removed
   `SIMPLE_BOOT_MINIMAL=1` (matching `check-simpleos-riscv64-kernel-link.shs` and
   `scripts/check/rebuild-sosix-qemu-media.shs`) so `rt_extras.c`/`primitives.c`/
   `freestanding_*` are linked, and registered the script in `scripts/check/guard_wiring_optout.txt`.
2. `src/os/compositor/browser_compositor_backend.spl` & `hosted_backend_winit.spl`:
   updated stale `os.drivers.framebuffer.fb_font.{get_glyph_8x16}` imports to
   `common.ui.glyph_bitmap_8x16.{get_glyph_8x16}`.
3. `src/os/apps/terminal/terminal.spl`: moved `me build_ui() -> UISession:` out of
   `BufferingTerminal` into `Terminal` (which defines `cols` and `rows`) and exported
   `Terminal, BufferingTerminal`.
4. `src/os/apps/shell/_ShellTools/system_tools.spl`: replaced `mode_text.parse_u64()`
   in `tool_chmod` with `_parse_chmod_octal(mode_text)` validating octal `'0'..'7'`
   digits and `0..0o7777` bounds.
5. `src/os/kernel/loader/{installed_artifact_boot_composition_v1,simplebox_catalog_media_boot_v1,simplebox_pinned_catalog_image_v1,simplebox_signed_catalog_boot_ingestion_v1}.spl`:
   passed explicit trailing enum arguments at all 44 single-arg `_fail_v1` /
   `_fail_after_cleanup_v1` / `_pinned_fail_v1` / `_ingestion_fail_v1` call sites.
6. `src/os/tools/shell/ls/ls_tool.spl`: imported `DirEntry` and typed
   `var entries: [DirEntry] = []` in `tool_ls`.
7. `src/lib/common/window_protocol/window_protocol.spl` & `src/os/userlib/_Window/client_methods.spl`:
   defined `pub struct WmStatus:` with explicit `WmStatus` type annotations on
   `WM_STATUS_OK`, `WM_STATUS_ERROR`, `WM_STATUS_NO_SPACE`, `WM_EVENT_FOCUS`,
   `WM_EVENT_RESIZE`, and imported `WmStatus` in `client_methods.spl`.

Verified compile + unit coverage (`x86_64_kernel_link_fixes_spec.spl` and related
unit specs pass on `/tmp/xc-llvm-seed-target/release/simple`), and kernel build
reaches `ld.lld` link with `compiled=926 failed=0`.

## Remaining 52 undefined symbols at link

`compiled=926` (all `src/os`, `src/lib`, `examples/09_embedded/simple_os` reachable
by `--entry-closure`) links against `examples/09_embedded/simple_os/arch/x86_64/boot/*`
(`up2_dci_uefi_loader.c` fails to compile due to missing `'efi.h'`, unused by
`os_entry.spl`; `type_stubs.c` + `auto_stubs.c` still sit in `x86_64/boot/` and
supply 3 weak/stub definitions `spl_dlclose`, `spl_dlsym`, `spl_wffi_call_i64`).
52 undefined symbols remain:

- **Compiler trait-default dispatch (1):**
  `wt_xc_x64_link__src__lib__gc_async_mut__gpu__engine2d__backend__RenderBackend.read_pixels_region`
  (called statically from `Engine2D.read_pixels_region` on trait receiver `self.backend: RenderBackend`).
- **Host-only GPU / Font / Process / File symbols pulled in by the 926-file closure (25):**
  `rt_cuda_device_identity`, `rt_directx_execute_readback_checked`,
  `rt_directx_hardware_adapter_identity`, `rt_font_bitmap_xoff`,
  `rt_font_bitmap_yoff`, `rt_file_read_regular_no_follow_bounded_bytes`,
  `rt_file_read_regular_no_follow_last_failure`, `rt_io_file_close_value`,
  `rt_io_file_open_append`, `rt_io_file_open_read`, `rt_io_file_open_write`,
  `rt_process_is_piped_alive_ref_v1`, `rt_process_run_bounded`,
  `rt_process_run_bounded_tuple`, `rt_process_run_tuple`,
  `rt_process_validate_piped_owned_v2`, `rt_process_validate_piped_ref_v1`,
  `rt_vulkan_compile_spirv_array`, `rt_vulkan_copy_to_buffer_u32`,
  `rt_vulkan_copy_u32_slots`, `rt_vulkan_create_compute_pipeline_raw`,
  `rt_vulkan_device_driver_identity`, `rt_vulkan_readback_u32_array`,
  `rt_vulkan_readback_u32_array_checksum`, `rt_vulkan_readback_u32_checksum`.
- **Missing freestanding `rt_*` core runtime helpers (26):**
  `rt_any_lt`, `rt_any_to_int`, `rt_array_copy`, `rt_array_data_ptr`,
  `rt_array_fill_span`, `rt_array_get_text`, `rt_array_is_byte_packed`,
  `rt_array_set_text`, `rt_array_write_span`, `rt_atexit_check`,
  `rt_byte_array_new_len`, `rt_dict_contains`, `rt_fs_read_text`,
  `rt_is_interpreter_runtime`, `rt_is_jit_runtime`, `rt_numeric_contains_u64`,
  `rt_raw_i64_to_string`, `rt_signal_check`, `rt_slice_text_bytes`,
  `rt_string_char_count`, `rt_string_free`, `rt_text_is_ascii`,
  `rt_to_int_dynamic`, `rt_typed_bytes_u8_data_at`, `rt_typed_words_u64_at`,
  `rt_unwrap_or_value`.

## Also: `--entry-closure` does not narrow this build

The x86_64 entry still pulls in shell, terminal, compositor, engine2d (Vulkan/CUDA/DirectX),
loader, userlib, and host SFFI modules; 926 files are compiled (vs ~300 on riscv32/arm32/i686).
Narrowing `--entry-closure` or pruning whole-module pulls is needed to decide which of
the 25 host-only symbols and 26 `rt_*` helpers are legitimately reachable from `os_entry.spl`.

## Next steps

1. Audit `--entry-closure` on `examples/09_embedded/simple_os/arch/x86_64/os_entry.spl` to stop pulling host GPU/DirectX/CUDA/Vulkan/process/SFFI modules into the freestanding kernel.
2. Provide canonical implementations (audited against `x86_64/boot/rt_extras.c` heap layouts) for any legitimately reachable `rt_*` helpers, and fix `RenderBackend.read_pixels_region` trait-default emission/dispatch in the compiler.
3. Re-run `check-simpleos-x86_64-kernel-link.shs --link-only` until 0 undefined symbols.

Until then the gate stays an honest FAIL (never a pass).
