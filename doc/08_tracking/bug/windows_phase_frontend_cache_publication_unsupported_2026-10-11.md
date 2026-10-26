# Windows phase frontend cache publication is unsupported

Status: OPEN_SOURCE_ESTABLISHED. Bug DB reconciliation pending.

The current Windows host cannot qualify the requested persisted phase frontend
reuse through the production compatibility boundary:

- `src/compiler/00.common/cache/phase_compatibility_path_io.spl` rejects the host
  when `rt_path_separator()` differs from `/` in directory and manifest admission.
- `src/runtime/runtime.c` returns zero from
  `rt_file_copy_create_excl_no_follow` and
  `rt_file_link_create_excl_no_follow` under `_WIN32`.
- Their Rust runtime twins in
  `src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs` return false on
  non-Unix hosts, including Windows.

These are direct source branches, not a measured cause of general compile latency.
Fixing a fixture's relative root alone cannot make its Windows publication pass.
Same-header reuse, cross-header portability and single-flight are separate gates.

Astra owns a private Windows boundary repair with actual runtime and pure-Simple
counterparts. Retain exclusive/no-replace publication, regular-file/no-follow
checks, UTF-8 paths, correct canonical drive/separator handling, and failure
cleanup. Removing the unsupported guard without implementing the operations
would be incorrect. Preserve other-session edits in the shared runtime owner.

Required actual-owner cases: successful copy/publication, existing destination
unchanged, missing source, directory/reparse source rejection, UTF-8 path roundtrip,
containment boundaries, and cleanup after a real failed copy. Qualify native
memory/time and implementation parity before admission. No tests have run for
this repair and no source patch has been applied.

Trusted immutable snapshot roots remain the diagnostic assumption. No hostile
ancestor-reparse confinement claim is made without an implemented boundary.
