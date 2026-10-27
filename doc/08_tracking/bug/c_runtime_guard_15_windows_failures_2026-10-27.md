# check-c-runtime-compiles-push: 15 pre-existing failures on Windows (llvm-mingw clang) - 2026-10-27

`CC=clang sh scripts/check/check-c-runtime-compiles-push.shs` on a Windows host
(llvm-mingw 20260922 ucrt, clang 23, target x86_64-w64-mingw32) reports
`FAIL - 15 file(s) failed to compile`. Identical on the base before PR #5047; none are
caused by it. They are POSIX/Linux/ARM-only files compiled without a platform guard,
so the guard cannot be green on Windows:

| file | error |
|---|---|
| providers/vector/bitmap_neon.c, http_neon.c | `<arm_neon.h>` only for ARM/AArch64 |
| providers/vector/bitmap_sve.c, http_sve.c | `arm_sve.h`: unknown type `__SVInt8_t` |
| runtime_bootstrap_linux_provider.c | undeclared `lstat` |
| runtime_sqlite_demand.c | `#error` requires Linux sealed snapshots |
| startup/baremetal/atomic_runtime.inc.c, atomic_slot_owner.inc.c | unknown type `spl_i64` (include fragments, not standalone TUs) |
| test/bootstrap_linux_provider_selfcheck.c | undeclared `symlink` |
| test/cpu_query_warm_cost.c | undeclared `cpu_set_t` |
| test/rt_bounded_read_allocation_selfcheck.c | undeclared `O_NOFOLLOW` |
| test/rt_cache_host_unix_sealed_v2_selfcheck.c | undeclared `EIO` |
| test/rt_file_publish_directory_macos_selfcheck.c | macOS-only call signature |
| test/rt_hosted_safe_artifact_v1_selfcheck.c | undeclared `openat` |
| test/vector_provider_test_events.c | undeclared `unsetenv` |

Fix (per file, in the file or in the guard):
- wrap ARM-only vector providers in `#if defined(__aarch64__) || defined(__ARM_NEON)` /
  SVE equivalents (empty TU otherwise);
- wrap Linux/POSIX-only sources and selfchecks in `#if !defined(_WIN32)` (empty TU
  otherwise) or give them a `_WIN32` stub, like `rt_win_excl_file_selfcheck.c` does;
- exclude `*.inc.c` fragments from the standalone scan (they are `#include`d, never
  built alone);
- keep the guard fail-closed: a platform-guarded empty TU still counts as compiled.
Then the guard can be green on Windows and added to the Windows lane.
