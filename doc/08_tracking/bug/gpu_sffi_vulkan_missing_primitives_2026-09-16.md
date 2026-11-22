# sffi_vulkan lost primitives backend_vulkan still imports (2026-09-16)
## Resolved 2026-11-22 — all `sffi_vulkan` primitives & `ffi_vulkan` canonical owner imports verified

## Observed
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:60-83` imports from
`std.nogc_sync_mut.gpu.engine2d.sffi_vulkan`:
`vulkan_sffi_readback_u32_alloc`, `vulkan_sffi_readback_u32_alloc_checksum`,
`vulkan_image_upload_note`, `vulkan_image_upload_last_mode`,
`vulkan_image_upload_last_reason`, `vulkan_image_upload_u32_requested` —
none of which are defined in
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` (only
`vulkan_sffi_readback_u32_into` at :883 remains). Every gpu test run emits
`[use-warning] ... does not provide it`, and
`engine_branch_coverage_spec.spl` fails outright with
`semantic: function 'vulkan_sffi_readback_u32_alloc' not found`
(backend_vulkan.spl:2193,2232,2305,2497 call it). The same spec also shows
`method 'backend_name' not found on type 'dict'` with a receiver value that
is a module-namespace dict — a suspected import-resolution defect where the
`Engine2D` value from `create_with_backend_strict`'s Ok arm resolves to the
module namespace.

## Impact
Vulkan readback paths and upload telemetry are uncallable; specs covering
them (engine_branch_coverage, draw_ir_adv_branch_coverage — the latter also
hits `MESA: error: Opening /dev/dri/card0 failed: Permission denied` with no
env guard in the spec) cannot go green on this host.

## Expectation
sffi_vulkan.spl provides every primitive backend_vulkan.spl imports (or
backend_vulkan's import list is pruned to what exists and call sites
migrate); the dict-receiver resolution is root-caused separately.

## Unblock condition
Restore/implement the six missing `vulkan_sffi_*` / `vulkan_image_upload_*`
functions in `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`; then
re-run the two branch-coverage specs (on a host with /dev/dri access or
behind an env guard) and confirm no `[use-warning]` for them.

## Resolution & Verification (2026-11-22)

- `vulkan_sffi_readback_u32_alloc` and `vulkan_sffi_readback_u32_alloc_checksum` are implemented in `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`, and `vulkan_image_upload_note`, `vulkan_image_upload_last_mode`, `vulkan_image_upload_last_reason`, and `vulkan_image_upload_u32_requested` live in `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl` (matching `backend_vulkan.spl`'s imports).
- Fixed the remaining `[use-warning]` source in `src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl`, which imported `rt_vulkan_*` from `std.gpu.engine2d.sffi_vulkan` (resolving first to `gc_async_mut/gpu/engine2d/sffi_vulkan.spl` instead of the `nogc_sync_mut` owner); pointed `ffi_vulkan.spl` directly at `std.nogc_sync_mut.gpu.engine2d.sffi_vulkan`.
- Verified `test/01_unit/lib/gpu/engine2d/engine_branch_coverage_spec.spl`: zero `[use-warning]`, zero `vulkan_sffi_readback_u32_alloc not found`, and `create_with_backend_strict` / `probe_backend` / all 55 Vulkan & Engine2D examples pass.
