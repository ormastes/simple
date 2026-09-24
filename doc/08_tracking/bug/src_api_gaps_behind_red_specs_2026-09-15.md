# Assorted src-side behavior gaps behind remaining RED specs
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected specs (left RED) — observed failure
- web_framework/session_csrf_signing_spec.spl — compute_signature returns
  `0000...` instead of the openssl HMAC-SHA256 oracle digest (3 its)
- file_read_single_return_type_spec.spl — 2 definitions of file_read now
  return an optional; spec pins the plain-text total return (3 its)
- concurrent_thread_lifecycle_spec.spl — repeated terminal cleanup returns
  Option::Some(0) where nil is pinned
- concurrent_thread_pointer_spawn_spec.spl — closure-pointer spawn check false
- channel_scalar_abi_spec.spl — scalar ABI checks fail
- js/engine_spec.spl (and sibling) — engine behavior failures
- test_runner/native_binary_resolution_spec.spl — capture truncation
- gpu_lighting3d_spec.spl, vulkan_backend3d_spec.spl (make_draw_cmd /
  make_bind_font_texture_cmd missing), engine/render/shader_compile_spec.spl
  (5 its, incl. len() on i64), gpu/gpu_queue_usm_spec.spl (4 its)
- linalg/raw_memory_owner_spec.spl — ptr/raw.spl renamed raw_f64_to_bits →
  spl_f64_to_bits / raw_bits_to_f64 → spl_bits_to_f64, and the spec's exact
  source pins (import strings, call counts) no longer match src
- ui/ui_scene_column_arena_v2_spec.spl — 3 behavioral assert failures
- enterprise_store specs failing on behavior (see individual logs)

## Unblock condition
Per spec: fix the src behavior or deliberately re-pin the spec after review.
None were weakened during triage.

- fs_driver/positioned_binary_backend_parity_spec.spl — `pread_bytes_handle` /
  `pread_bounded_bytes_handle` missing on DbFsDriver (only the text-returning
  `pread_handle` exists in src/lib/nogc_sync_mut/db/dbfs_driver/namespace_io.spl)

