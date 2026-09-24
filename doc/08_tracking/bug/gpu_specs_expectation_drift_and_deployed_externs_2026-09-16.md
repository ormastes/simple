# GPU spec expectation drift + deployed-binary extern gaps (2026-09-16)

## Observed (A — expectation drift, lib behavior changed under the specs)
- `glyph_spec.spl`: packed glyph rows shifted by one column
  (`expected [0,31,2,4,8,31,0] to equal [0,0,31,2,4,8,31]` etc.).
- `helpers_text_spec.spl`: advance-gap checks now `expected 5 to be less than 5`
  (gap equals the bound, not below it).
- `bitmap_font_offload_spec.spl`: CUDA provenance string changed from
  `bitmap-font-glyphs-rasterized-on-cpu-then-uploaded` to
  `bitmap-font-gpu-raster-kernel-ready-readback-required`.
- `ffi_vulkan_spec.spl`: `last_rejection()` empty where `shutdown` expected.
- `backend_rocm_text_fallback_spec.spl`, `compute_dispatch_spec.spl`,
  `backend_software_simd_spec.spl` (AC-6 simd-hit counters),
  `web_draw_ir_damage_consumer_branch_coverage_spec.spl`,
  `draw_ir_adv_native_optional_contract_spec.spl`,
  `opencl/rocm/cuda_session_contract_spec.spl`,
  `generated_kernel_dispatch_spec.spl`,
  `vulkan_sffi_provider_ownership/parity_spec.spl`: plain
  expected/actual mismatches with no missing symbol.
- `ffi_dispatch_spec.spl`: `spl_dlopen failed for 'nonexistent_libvulkan.so.999'`
  raises a runtime error instead of returning nil (AC-8 wants graceful nil).
- `probe_layer_overlap_hit_test.spl`: not a spec — an evidence script for
  `bin/simple run` with zero `# @di_test` examples; the test runner correctly
  reports `no examples executed`. It should not be counted as a failing spec.

## Observed (B — `unknown extern function` though lib source defines them)
`cuda_public_surface_spec.spl` (`rt_cuda_stream_create` — defined in
`src/lib/nogc_sync_mut/cuda/sffi.spl`), `font_compat_spec.spl`
(`rt_font_load` — `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`),
`ffi_out_param_via_return_value_detection_spec.spl` (`rt_fs_read_text` —
`src/lib/nogc_sync_mut/sffi/fs.spl`). The runner's child binary is
`bin/release/aarch64-unknown-linux-gnu/simple` (wrong-arch deployed binary
class, see memory note "MCP points at wrong arch"); the deployed runtime
does not export these externs even though the source declares them.

## Impact
~14 specs stay RED; class A hides real behavior changes (glyph packing,
bitmap font offload policy) that no other test guards; class B blocks any
extern-dependent gpu spec on this host.

## Expectation
A: decide per spec whether the new behavior is intended (update expectation
with the owning lane's sign-off) or a regression (fix lib). B: redeploy the
correct-triple self-hosted binary so declared externs resolve, then re-run.

## Unblock condition
A: per-spec disposition recorded; B: `readlink -f bin/simple` points at the
x86_64 self-hosted release and the three specs re-run green or reclassified.
