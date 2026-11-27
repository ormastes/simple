# Seed native_project tests require an external SQLite SDK (Windows)

Found 2026-11-03 running `cargo test --lib -p simple-compiler pipeline::native_project` on
Windows (CC=clang-cl). Two tests fail only because no real SQLite SDK exists on the host:

- `tools::llvm_tool_policy_tests::bootstrap_tools_sqlite_sdk_loads_adjacent_dll_without_sdk_path`
  (`prepare_bootstrap_tools_sqlite_sdk` demands `C:/msys64/{clang64,ucrt64,mingw64}` sqlite3.h +
  libsqlite3.dll.a + libsqlite3-0.dll).
- `tests::test_stage4_c_runtime_archive_includes_hosted_font_and_sqlite`
  (`src/runtime/runtime_sqlite.c:17` `#include <sqlite3.h>`: file not found).

Both contradict CLAUDE.md "No external SQLite": `rt_sqlite_*` must be backed by the embedded engine
(`src/lib/nogc_sync_mut/db/dbfs_engine/`), not a dev package (owner decision todo 285). The tests are
correct as written; the fix is to back `rt_sqlite_*` in the C runtime / bootstrap-tools lane with the
embedded engine so no SDK is needed. Not a Windows test-environment fix.

## 2026-11-06 resolution (fixed)

Policy: user decision 2026-11-04 exempts the Rust SEED (bootstrap-only) from the
"no external SQLite" rule; pure-Simple lanes keep the embedded engine and never
link libsqlite3. The tests were correct; two gaps remained:

1. Host lacked the SDK: `pacman -S mingw-w64-clang-x86_64-sqlite3` provides
   `C:/msys64/clang64/{include/sqlite3.h,lib/libsqlite3.dll.a,bin/libsqlite3-0.dll}`;
   `bootstrap_tools_sqlite_sdk_loads_adjacent_dll_without_sdk_path` then passes.
2. Real code gap: `build_c_runtime_library` (stage4 hosted lane) compiled
   `runtime_sqlite.c` with no SDK include dir (only the bootstrap-tools lane had
   discovery). Added `stage_windows_sqlite_header_include` (tools.rs): stages ONLY
   `sqlite3.h` into `<build_dir>/sqlite-sdk-include` and passes `-I` for
   `runtime_sqlite.c` only. Prevention test
   `stage4_runtime_sqlite_header_staging_exposes_only_sqlite3_h`.
Result: `test_stage4_c_runtime_archive_includes_hosted_font_and_sqlite`,
`bootstrap_tools_sqlite_sdk_loads_adjacent_dll_without_sdk_path` and the new test
all pass (3/3).
