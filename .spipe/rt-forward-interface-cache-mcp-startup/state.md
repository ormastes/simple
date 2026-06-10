# Feature: rt-forward-interface-cache-mcp-startup

## Raw Request
$sp_dev even use rt by forwarding. it must not awarkward. no duplication feature with existing. it seems just chang rt by forwarding. 1. proper hamoney forward rt with simple std lib. 2. import seems just import whole content, cache interface only, when loading script background make interface only later check modified time and check cache valid if valide load interface only then call/used load whole. 3. check whole mcp app exist in simple include example. specially loading time. and fix and deploy local.

## Task Type
bug

## Refined Goal
Make MCP and script startup use the existing std/lib runtime forwarding and interface-cache mechanisms so startup handshakes do not require direct rt calls or eager full-module loading.

## Acceptance Criteria
- AC-1: App-level MCP/LSP code and MCP stdio integration specs contain no direct `rt_*` or `extern fn rt_*` usage; runtime access goes through std/lib forwarding facades.
- AC-2: Runtime-forward cache refresh reuses the existing cache artifact and exposes a deterministic validity signal that fails when the cache is stale or missing.
- AC-3: Import startup has an executable regression check proving a valid interface cache can be used without eagerly loading full module content, and cache invalidation is based on source modified time.
- AC-4: Simple MCP and Simple LSP MCP native servers both complete framed stdio handshakes (`initialize`/`tools/list` where applicable) from local deployment artifacts.
- AC-5: MCP startup verification records startup timing and fails on missing native artifacts, raw-source fallback, malformed framed output, or hidden direct-rt regressions.
- AC-6: Local deployment updates the runnable `bin/simple_mcp_server` and `bin/simple_lsp_mcp_server` wrappers/artifacts only after the native smoke and startup checks pass.

## Scope Exclusions
- No new runtime facade system that duplicates existing `std.nogc_sync_mut.io.*` or app re-export facades.
- No broad compiler import redesign beyond the minimal cache-validity/startup regression needed for this bug.
- No release tag or public npm publish.

## Phase
verify-done

## Log
- dev: Created state file with 6 acceptance criteria (type: bug).
- impl: Switched MCP/cache verification paths from direct `rt_*` calls to existing std/lib forwarding surfaces, added rt-forward cache validity checks, and added SHB/source-mtime interface-cache fast-path support.
- impl: Added executable regressions for SHB mtime round-trip and binary I/O little-endian mask correctness; fixed `binary_io` byte masking and `Option.map(...)` runtime issues reached by the real SHB path.
- impl: Patched watcher inline SHB fallback to persist source-mtime metadata via `shb_write_with_source_mtime(...)` so background-generated caches follow the same fast-path contract as watcher-managed caches.
- verify: Local native deploy is current. `bin/simple_mcp_server` and `bin/simple_lsp_mcp_server` were rebuilt from local native artifacts and `scripts/check/check-mcp-native-smoke.shs` passes with framed MCP/LSP handshakes, `rt_forward_cache_valid=true`, interface-cache stale/body rejection, and startup timings under the 5000ms gate.
- verify: Focused tests pass: `test/01_unit/compiler/cache/shb_mtime_spec.spl`, `test/01_unit/lib/io/binary_io_spec.spl`, `test/02_integration/app/mcp_stdio_integration_spec.spl`, and `test/02_integration/watcher/watcher_shb_integration_spec.spl`.
- verify: Required broad compiler verification is still not green for the repository as a whole. `SIMPLE_LIB=src bin/simple check src/compiler --mode=interpreter` was driven much deeper by export-surface fixes, but the latest 600s run still fails with unrelated HIR/AST/type-system export errors outside this MCP/cache lane. Completion is therefore not yet proven against the repo-wide compiler gate.
- verify (2026-06-10): Repo-wide compiler gate now green: `SIMPLE_LIB=src bin/simple check src/compiler --mode=interpreter` → "All checks passed (2659 file(s))", exit 0.
- impl (2026-06-10): AC-1 regression closed: purged ~340 direct `rt_*` externs/calls from src/app/mcp (14 files), src/app/mcpgdb (12), src/app/simple_lsp_mcp (4), src/app/ui.mcp (1), src/app/serial_mcp (1); routed through `std.io_runtime` + `std.nogc_sync_mut.io.{file_ops,process_ops,dir_ops}` facades; added thin io_runtime wrappers (file_append_text, dir_list, process_spawn_async/is_running/kill).
- verify (2026-06-10): `scripts/check/check-mcp-native-smoke.shs` exit 0 — all six *_direct_rt_valid=true, interface_cache_valid=true (stale + body rejection), rt_forward_cache_valid=true, framed MCP/LSP handshakes valid (151/11 tools), mcp_startup_ms=2707, lsp_mcp_startup_ms=51 (< 5000 gate). Focused specs pass: shb_mtime_spec, binary_io_spec, mcp_stdio_integration_spec, watcher_shb_integration_spec. AC-1..AC-6 all verified.
