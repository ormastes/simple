# native_capsule_result_receipt_spec: stale arity (fixed) + file_fsync fails on Windows /tmp object

- Date: 2026-10-27 | Spec: test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl (7/8 -> 8/9 declared; 1 fail left)
- Cause A (FIXED): spec called `driver_native_collect_capsule_result_v1(receipt_ctx(), batch, cache, name, path)`;
  the function (driver_aot_native_output.spl:1233) takes 4 args (ctx parameter removed). Dropped `receipt_ctx()`
  at both call sites in the spec. (`receipt_ctx()` helper at line 17 is now unused; delete it if desired.)
  The `[T]` mentioned in the original report is not in source: cas_batch_transaction.spl already uses `<T>`.
- Cause B (OPEN): "binds object bytes size path identity and frozen inputs" now fails with
  `native-capsule-object-fsync-failed:receipt: /tmp/aot-<hash>.o` — `file_fsync(object_path)`
  (src/lib/nogc_sync_mut/io/file_ops.spl:389 -> `rt_file_fsync(host_path_native(path))`) returns false for the
  /tmp path on Windows (likely the seed runtime opens read-only for FlushFileBuffers, or /tmp is not mapped).
  The runtime lives in src/compiler_rust (off-limits here). Next step: check rt_file_fsync's Windows open flags
  (needs GENERIC_WRITE) and /tmp mapping in host_path_native.

## Correction (review of PR #4957)
Cause B (the file opened read-only) is ruled out: `win_fsync_path` (runtime file_ops.rs:870-897) already opens with FILE_GENERIC_READ|FILE_GENERIC_WRITE. The remaining candidate is how `host_path_native` maps `/tmp` to the drive root.
