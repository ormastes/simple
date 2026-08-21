# Stage4 localized runtime legacy compatibility provider

Mirror of `test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl`.

The executable SSpec checks archive naming and symbol formats across hosted ABIs, the audited compatibility export set, localization of non-exports, rejection of missing/duplicate/unsafe globals, the sole runtime dependency, cycle resolution, and build/localize/admit/cleanup behavior.

This is static ABI and pipeline evidence; it does not execute the compatibility archive on every platform.
