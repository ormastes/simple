---
id: lsp_mcp_server_process_leak_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Manual process audit (pkill)
related: bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server
related: .mcp.json
related: config/t32/t32_lsp_mcp_config.json
related: config/obsidian/obsidian_lsp_mcp_config.json
---

# LSP MCP Server: 48 orphaned processes with no cleanup

## Summary

Native `simple_lsp_mcp_server` binary (`bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server`) spawned 48 simultaneous orphaned processes on 2026-07-05 that accumulated without termination. Processes were killed manually via `pkill`. Root cause is unknown — suspected spawners are IDE/LSP integrations (VSCode extension, T32, Obsidian) or check scripts launching the binary per-request without connection reuse or graceful termination. The `.mcp.json` config intentionally does NOT use the native binary (uses `bin/mcp_stdio_bridge.js` instead), so the leak source is external to that config.

## Evidence

- Process count: 48 orphaned `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server` instances running simultaneously
- Termination method: manual `pkill simple_lsp_mcp_server`
- No graceful shutdown observed on any instance
- Spawning pattern: continuous or event-driven repetition without cleanup/reuse
- Date discovered: 2026-07-05

## Impact

- Process resource leak (file descriptors, memory, threads per instance)
- Potential port/socket exhaustion if servers bind to fixed ports or sockets
- IDE/editor responsiveness degraded by competing LSP processes
- Each orphaned process consumes startup latency + memory footprint

## Scope

The spawner is NOT `.mcp.json` (which explicitly uses `bin/mcp_stdio_bridge.js`). Suspects:
1. **VSCode extension** — may be restarting the native LSP server per file/request without reuse
2. **T32 integration** — `config/t32/t32_lsp_mcp_config.json` may spawn the server repeatedly
3. **Obsidian plugin** — `config/obsidian/obsidian_lsp_mcp_config.json` may lack lifecycle management
4. **Check scripts** — any `scripts/check/` or `scripts/verify/` script launching the server for validation

## Next Steps

1. Audit all callers of `simple_lsp_mcp_server`: grep configs/, scripts/, and vendor MCP registry for spawn patterns
2. Check `~/Library/Logs/` and IDE application logs for error patterns (handshake failures, timeout loops)
3. Instrument the native server with a single-instance guard (lockfile or socket-based) and add idle-exit timeout (e.g., 5 min no requests → exit)
4. Update each spawner to: (a) reuse connections across requests, (b) signal graceful shutdown on client disconnect, or (c) use connection pooling
5. Verify cleanup on normal exit and SIGTERM handling

## 2026-07-19 source audit update

The original 48-process observation remains real, but the server-child attribution is unproven: it recorded no PID/PPID, start command, open-stdin owner, log, or reproducible launcher. Current `.mcp.json` directly launches `bin/simple_lsp_mcp_server`; the named T32 and Obsidian config files no longer exist. The stdio server owns no background daemon, blocks on input, and exits on EOF. Do not add a singleton or idle timer until the external client owner is captured, because independent MCP clients require isolated stdio processes.

The focused lifecycle gate should launch the exact wrapper with a tracked PID, initialize it, close stdin, bounded-wait for that PID to exit, repeat three times, and assert only those tracked PIDs are gone. A separate confirmed risk exists in opt-in diagnostics: its `simple check` subprocess uses direct-child timeout cleanup instead of the existing process-group-aware bounded API.

The diagnostics risk is now fixed in source: the opt-in call uses
`process_run_bounded` with its existing 10-second deadline and a 1 MiB output
cap, and a focused regression rejects restoration of `process_run_timeout`.
This does not identify or resolve the external owner of the original 48 server
processes; the tracked-PID EOF lifecycle gate remains pending.
