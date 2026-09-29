# macOS Stage 2 compiler tests: full-CLI `host-gpu` link has 170 undefined symbols

Status: open, 2026-09-27. Host: M4 mac, aarch64-apple-darwin. Tree: `origin/main`
with #1785 and #1792. Bootstrap command:
`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=10
--produce-stage3-receipt=verify-landed-compiler-fix` with
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0 BOOTSTRAP_VERIFY_BUILD_THREADS=10
BOOTSTRAP_VERIFY_TEST_WORKERS=10 BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT=1800`.

## What passes

Stage 2 builds, links, and is admitted. The Stage 3 planner receipt is produced.
In the phase verification matrix, `compiler_version` passes. `compiler_cli_build`
compiles all 2,447 full-CLI units in 699 s.

At the default settings (3 build threads, 600 s per-file timeout, host load ~20),
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` hit the per-file timeout.
It cleared only at 10 threads.

## What fails

The final link of `compiler_cli_build` (`--runtime-bundle host-gpu`) reports
170 undefined symbols (`ld: symbol(s) not found for architecture arm64`). Every
later matrix row is BLOCKED or UNSUPPORTED.

The `host-gpu` lane in `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
links the frozen hosted-runtime rlib (`deps/libspl_hosted_runtime-*.rlib`) plus a
freshly built core-C supplement. It does not link `libsimple_native_all.a`; this
is intentional ("limited to the Simple/C core ABI").

- **121 symbols** are defined in the capsule's `libsimple_native_all.a` but not
  provided by the lane:
  - Rust `std`/`alloc` symbols referenced by the hosted rlib. The std shim
    (`build_rust_std_shim_for_rlib`) is `#[cfg(target_os = "windows")]` only, so
    macOS links the rlib with no std.
  - `rt_metal_*`, `rt_cuda_*`, `rt_engine2d_rocm_*`, Vulkan SFFI,
    `rt_font_load_array`, `rt_write_u32s_to_raw`, and others.
- **49 symbols** are defined in no runtime archive:
  - SDL: `rt_sdl_*`, `rt_sdl2_clipboard_*`.
  - `rt_sqlite_*`: the embedded-SQL mapping gap. This is an owner decision
    (todo 285); never back it with `libsqlite3`.
  - `rt_arm_array_get_byte_u32`, `rt_arm_array_len_u32`.
  - Unmangled method symbols `DbFsDriver.pread_bytes_handle` and
    `Trace32Client.wait_for_stop`. This is a separate codegen defect.
  - `_gpu` and `lib__editor__extensions__builtin__spl_language__spl_language_manifest`.

## Context

The Linux counterpart fails earlier, at HIR field inference
(`linux_stage2_full_cli_hir_field_inference_2026-09-27.md`). The Stage 2 matrix
has not passed on any platform yet.

Seed delegation (the default, `BOOTSTRAP_STAGE2_TEST_DELEGATE=1`) needs an owner
MC/DC-off waiver (`SIMPLE_MCDC_OFF_WAIVER_{REASON,REVIEWER,REVIEW_ID,VERSION}`),
which the script never defaults.

## Next

Decide the full-CLI provider set for `host-gpu` on Darwin: either a std shim plus
the GPU/font providers, or a different lane for the full CLI. Then fill or waive
the 49 unprovided symbols per owner decisions. Separately, fix the unmangled
method-symbol emission.

Logs:
`.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/{summary.env,logs/compiler_cli_build.log}`.
