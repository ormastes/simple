<!-- codex-research -->
# Runtime Facade Optimization - Local Research

## Scope

This research covers the rule that applications and scripts should use std-facing
Simple APIs while runtime-backed optimization remains hidden behind library
facades, generated bindings, or startup caches.

## Findings

- MCP app code currently uses the std transport facade:
  `src/app/mcp/main_lazy_protocol.spl` imports
  `std.mcp_sdk.transport.stdio.{mcp_stdio_read_message}` and has no direct
  `rt_stdin*` or `rt_mcp_write*` references.
- The runtime-backed MCP stdio bindings are isolated in
  `src/lib/nogc_sync_mut/mcp_sdk/transport/stdio.spl`. That file exposes
  `mcp_stdio_read_line`, `mcp_stdio_read_bytes`, and
  `mcp_stdio_read_message`, while the runtime symbols remain private to the
  facade implementation.
- The rt-forward cache refresh is implemented by
  `scripts/setup/refresh-rt-forward-cache.shs`. It records std-to-runtime
  mappings under `.simple/cache/rt-forward/stdio.sdn` and hashes the runtime and
  stdio source inputs.
- The MCP native smoke validator checks the cache mapping, framing validity,
  tool schema, and the previous bogus huge `Content-Length` failure.
- The MCP integration spec no longer declares direct runtime file/process
  externs. It uses `std.nogc_sync_mut.io.file_ops.file_write` and
  `std.process.run`.
- The same facade pattern now covers adjacent MCP servers and tooling lanes:
  `src/app/simple_lsp_mcp`, `src/app/serial_mcp`, `src/app/mcpgdb`, and
  `src/app/ui.mcp` have no direct `rt_*` references.
- `src/app/jj` now uses a local `app.jj.process_facade` over
  `std.process.run` plus the existing std/app CLI argument facade, so JJ command
  modules no longer bind `rt_process_run` or `rt_cli_get_args` directly.
- A generic `std.nogc_sync_mut.host.runtime_facade` now exposes `host_*`
  process, file, directory, cwd, env, and CLI argument helpers for non-MCP apps.
  `src/app/snpm` has been migrated to this facade and has no direct `rt_*`
  references.
- `src/app/simple_portal` has also been migrated to the generic host facade for
  CLI args, environment, file reads/writes, file existence, and directory
  creation.
- `src/app/plugin` now consumes the generic host facade for manifest file I/O,
  plugin-library existence checks, manifest directory creation, environment
  lookup, and home-directory resolution.
- `src/app/play`, `src/app/startup`, and `src/app/sj` now use the generic host
  facade for session-store file I/O, process execution, timestamps, byte reads,
  environment lookup, CLI args, and pid lookup.
- `src/app/watch` and `src/app/pkg` now use the generic host facade for file
  checks, file reads/writes, process execution, environment lookup, CLI args,
  directory walking, and file modification timestamps.
- `src/app/cli_debug`, `src/app/stats`, `src/app/optimize`,
  `src/app/simple_process_manager`, and `src/app/compile` now use the generic
  host facade for CLI args, process execution, pid/time/RSS, file I/O,
  byte-to-text conversion, and host socket/stdout/stderr helpers.
- Additional small app lanes now migrated to the same facade:
  `src/app/run`, `src/app/release`, `src/app/jupyter_kernel`,
  `src/app/grammar_doc`, `src/app/doc/public_check`,
  `src/app/llm_process_gen`, `src/app/md_lsp`, `src/app/task_daemon`,
  `src/app/spipe_process_harness`, and `src/app/test_dep_graph_shared.spl`.
- A later pass migrated more one-file and startup-light app lanes:
  `src/app/simpleos_nvme_serial_check`,
  `src/app/simpleos_board_serial_check`, `src/app/semihost`,
  `src/app/llm_diag_hook`, `src/app/linker_gen`, `src/app/check`,
  `src/app/linkers`, `src/app/info`, `src/app/env`, `src/app/sdn`,
  `src/app/test_cache_shared.spl`, `src/app/exp`, `src/app/replay`,
  `src/app/gen_lean`, `src/app/qemu`, `src/app/sim`, `src/app/js`, and
  `src/app/repl`.
- The latest pass migrated `src/app/cli`, `src/app/svllm_pack`,
  `src/app/spipe_docgen`, `src/app/sj_daemon`, `src/app/itf/main.spl`, and
  `src/app/package.registry` away from app-level `rt_*` calls. Package registry
  Ed25519 acceleration now goes through
  `src/lib/nogc_sync_mut/crypto/runtime_facade.spl`.
- `src/app/io/rt_compile_stub.spl` now exposes `compile_to_llvm_ir_stub`; the
  CLI bootstrap checker calls `app.cli.compile_stub_facade.cli_compile_to_llvm_ir`
  instead of a `rt_*`-named helper.
- A subsequent pass migrated `src/app/itf`, `src/app/web_stack_sample`,
  `src/app/ui.test_api`, `src/app/test_daemon`, and `src/app/test_runner_new`.
  New lib facades isolate runtime-backed HTTP, daemon process spawning,
  daemon health HTTP, coverage collection, and fork-mode test execution:
  `src/lib/nogc_sync_mut/http/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/daemon_runtime/*.spl`, and
  `src/lib/nogc_sync_mut/test_runner_runtime/*.spl`.
- `scripts/check/check-mcp-native-smoke.shs` guards the migrated lanes with
  direct-runtime scans and still validates `simple-mcp`, `simple-lsp-mcp`, and
  the rt-forward cache in one startup smoke.

## Policy

REQ-RTF-001: App and script code should not call `rt_*` directly for optimized
runtime paths.

REQ-RTF-002: Runtime-backed acceleration must be exposed through std-facing
facades, generated binding tables, or explicit startup caches.

REQ-RTF-003: Cache refresh must be explicit and validated in the same smoke path
that proves user-facing startup.

REQ-RTF-004: Direct `rt_*` extern declarations are acceptable only in runtime
binding/facade modules, low-level platform probes, or legacy tests not in the
touched feature lane.

## Current Evidence

- `simple-mcp`, `simple-lsp-mcp`, `serial-mcp`, `mcpgdb`, `ui.mcp`, and the MCP
  stdio integration spec all pass direct-runtime scans.
- Native smoke output reports:
  `mcp_app_direct_rt_valid=true`,
  `lsp_mcp_app_direct_rt_valid=true`,
  `mcpgdb_app_direct_rt_valid=true`,
  `ui_mcp_app_direct_rt_valid=true`,
  `serial_mcp_app_direct_rt_valid=true`,
  `mcp_stdio_spec_direct_rt_valid=true`,
  `mcp_framing_valid=true`,
  `lsp_framing_valid=true`, and
  `rt_forward_cache_valid=true`.
- Targeted checks pass for the newly migrated lanes:
  `./bin/simple check src/lib/nogc_sync_mut/host/runtime_facade.spl
  src/app/cli_debug src/app/stats src/app/optimize
  src/app/simple_process_manager src/app/compile src/app/run src/app/release
  src/app/jupyter_kernel src/app/grammar_doc src/app/doc/public_check
  src/app/llm_process_gen src/app/md_lsp src/app/task_daemon
  src/app/spipe_process_harness src/app/test_dep_graph_shared.spl`.
- Remaining direct runtime call-site files in `src/app` after the latest pass:
  `143` by `rg -l 'extern fn rt_|\brt_[A-Za-z0-9_]+\(' src/app | wc -l`.
  The largest groups remain `src/app/io`, `src/app/wm_compare`,
  `src/app/ui.web`, `src/app/gui_perf`, `src/app/ui`, and `src/app/debug`.
- Targeted direct-runtime scans now pass for `src/app/cli`, `src/app/svllm_pack`,
  `src/app/spipe_docgen`, `src/app/sj_daemon`, `src/app/itf/main.spl`, and
  `src/app/package.registry`.
- Targeted direct-runtime scans also pass for `src/app/test_daemon`,
  `src/app/test_runner_new`, `src/app/web_stack_sample`, and
  `src/app/ui.test_api`; their targeted checks pass with the new lib facades.
- Targeted checks pass for the new one-file/startup-light batch, except
  `src/app/sdn/commands.spl` emits a pre-existing unresolved import warning for
  `app`; it no longer has direct `rt_*` call sites.

## 2026-06-08 Runtime Facade Migration Checkpoint

- Added narrow std/lib facades for runtime-backed debug, memory, terminal,
  generic I/O, and winit window/event operations:
  `src/lib/nogc_sync_mut/debug/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/memory/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/terminal/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/io/runtime_facade.spl`, and
  `src/lib/nogc_sync_mut/ui/winit_runtime_facade.spl`.
- Extended `src/lib/nogc_sync_mut/host/runtime_facade.spl` with
  `host_process_run_timeout` and `host_file_write_bytes`.
- Migrated small real app buckets away from direct `rt_*`: debug backends,
  GC memory helpers, wrapper generator, web command, VM manager, QEMU/docker
  test helpers, SCV byte stdout, IPC stdin, shared MDI, TUI web, UI detect,
  UI CLI, TUI, Tauri/Electron file polling, Browser/Chromium winit calls, and
  `src/app/gui_perf`.
- Checks passed:
  `./bin/simple check src/lib/nogc_sync_mut/host/runtime_facade.spl
  src/lib/nogc_sync_mut/io/runtime_facade.spl
  src/lib/nogc_sync_mut/terminal/runtime_facade.spl
  src/lib/nogc_sync_mut/ui/winit_runtime_facade.spl
  src/lib/nogc_sync_mut/debug/runtime_facade.spl
  src/lib/nogc_sync_mut/memory/runtime_facade.spl`;
  targeted checks also pass for migrated debug, GC, test, UI, Tauri, Browser,
  Chromium, Electron, and `gui_perf` lanes. Broad app checks still report only
  pre-existing unresolved-import warnings in unrelated directories.
- Remaining direct runtime call-site files in `src/app`: `88`.
  Largest remaining groups: `src/app/io`, `src/app/wm_compare`,
  `src/app/ui.web` TLS/async internals, `src/app/ui.render`,
  `src/app/sffi_gen.templates`, and `src/app/svim`.

## 2026-06-08 Continued Migration Checkpoint

- Migrated additional app-facing lanes to std/lib facades:
  `src/app/ui.render`, remaining `src/app/ui` backend entry/loaders,
  one-file Browser/Chromium/Electron leftovers, `src/app/svim`,
  `src/app/ui.web`, and `src/app/wm_compare`.
- Added or extended facades for these migrations:
  `src/lib/nogc_sync_mut/test262/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/cli/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/io/runtime_facade.spl`,
  `src/lib/nogc_sync_mut/memory/runtime_facade.spl`, and
  `src/lib/nogc_sync_mut/host/runtime_facade.spl`.
- Migrated the `src/app/io` CLI/compile command path:
  `cli_ops.spl`, `cli_compile_part1.spl`, `cli_compile_part2.spl`,
  `cli_commands_part1.spl`, and `cli_commands_part2.spl`.
- Targeted checks passed for every migrated bucket:
  `src/app/ui.render`, `src/app/ui` root entry files,
  `src/app/ui.browser`, `src/app/ui.chromium`, `src/app/ui.electron`,
  `src/app/svim`, `src/app/ui.web`, `src/app/wm_compare`, and the
  `src/app/io` CLI/compile batch. `doc/06_spec` executable spec guard
  remains `0`.
- Remaining direct runtime call-site files in `src/app`: `45`.
  Real remaining implementation bucket: `34` files under `src/app/io`.
  Other matches are templates/audit/docs (`src/app/sffi_gen.templates`,
  `src/app/audit`, `src/app/perf/README.md`, `src/app/grammar_doc`).

## 2026-06-08 App Direct Runtime Cleanup Checkpoint

- Current app direct runtime scan is clean:
  `python3` scan for `\brt_[A-Za-z0-9_]+\s*\(` under `src/app/**/*.spl`
  reports `files 0 matches 0`.
- Converted exact duplicate app/io SFFI and host-operation modules into
  compatibility re-export facades over `std.nogc_sync_mut.io.*`, keeping
  app-facing import paths stable while moving runtime bindings behind the std/lib
  boundary. This reduced app direct runtime matches from `1054` to `0` in this
  pass.
- Moved `src/app/io/jit_sffi.spl` implementation behind
  `src/lib/nogc_sync_mut/io/jit_sffi.spl`; the app module now re-exports the
  std/lib implementation. The lib implementation uses `host_process_run` for the
  soft execution fallback rather than importing compiler internals from the app
  layer.
- Added `src/lib/nogc_sync_mut/io/hub_runtime_facade.spl` for legacy app.io hub
  helpers: env lookup, random, logging, and volatile i64 access. `src/app/io/mod.spl`
  now calls those non-`rt_*` std/lib wrappers.
- Added std/lib availability exports for `audio_available` and `window_available`
  so `src/app/io/feature_registry.spl` checks after the app facades moved to
  std/lib re-exports.
- Verification evidence:
  - `SIMPLE_LIB=src bin/simple check src/app/io/feature_registry.spl` passes.
  - `SIMPLE_LIB=src bin/simple check src/app/io/jit_sffi.spl src/lib/nogc_sync_mut/io/jit_sffi.spl` passes.
  - Representative re-export facade checks pass for migrated app/io modules.
  - `SIMPLE_LIB=src bin/simple check src/app/mcp` passes.
  - `SIMPLE_LIB=src bin/simple check src/app/simple_lsp_mcp` passes.
  - `sh scripts/check/check-mcp-native-smoke.shs` reports MCP/LSP framing and
    schema valid, all MCP-family app direct-runtime smoke flags true, and
    `rt_forward_cache_valid=true`.
  - `find doc/06_spec -name '*_spec.spl' | wc -l` reports `0`.
- Known unrelated broad-check blockers remain in `SIMPLE_LIB=src bin/simple check
  src/app/io`: unresolved exports in CLI/compiler helper modules (`TOK_EOF`,
  `runtime_cli_handle_compile`, `aot_file`, `CompileOptions`) and
  `std.common.types.Handle`. These are not direct runtime call sites and were not
  introduced by the runtime-facade migration.
