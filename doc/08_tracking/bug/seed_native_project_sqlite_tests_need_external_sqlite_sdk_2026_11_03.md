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
