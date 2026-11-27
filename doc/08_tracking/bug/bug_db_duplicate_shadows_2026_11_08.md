# Duplicate bug primary rows

At release commit `3eda0f35875c9cc2f0d1697886c5100ea49ff7e5`, the canonical tracking uniqueness gate failed with three IDs duplicated across `bugs_active` and `bugs`:

- `nativeall_text_byte_facade_exports_missing_2026_11_07`
- `s3_selfbuild_stale_surface_index_impls_backend_2026-11-07`
- `stage2_new3_native_build_worker_av_c01_2026-11-07`

Each `bugs` shadow was byte-identical to its `bugs_active` owner. Remove only those three shadows, retain the active rows, and leave all effective statuses and existing investigation history unchanged. This repairs tracking data; it makes no runtime verification claim.

Executed once on exact release blobs: `check-tracking-db-unique-ids.shs` exited 1, 3276 rows, three duplicate IDs. Executed once after removing the shadows: exit 0, 3273 rows, zero duplicate IDs. Full logs and exit codes are retained outside the worktree in `D:/dev/simple-warning-lint-audit-20261108/bug-db-unique-ids*.{log,exit}`.
