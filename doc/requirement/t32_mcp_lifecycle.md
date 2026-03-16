# T32 MCP Lifecycle Tools — Requirements

## Feature Name
T32 MCP Lifecycle Management: `t32_launch`, `t32_shutdown`, `t32_status`

## Motivation (Why)
The T32 MCP server has 23 tools for controlling TRACE32 sessions, but **no lifecycle management**. Users must manually start PowerView before using any MCP tools. This creates friction — especially in automated/CI workflows and for users unfamiliar with T32 setup.

Three tools close this gap:
1. **t32_launch** — Spawn PowerView from MCP (headless or visible)
2. **t32_shutdown** — Graceful process termination
3. **t32_status** — Installation discovery and process status

## Scope

### In Scope
- Spawn PowerView (t32marm) with configurable options (headless, port, config file, architecture)
- Xvfb integration for headless operation (SCREEN=INVISIBLE needs X11)
- Graceful shutdown via t32rem QUIT, fallback to process_kill
- Installation discovery: find T32 binaries, check versions, list configs
- Process discovery: find running T32 instances, their ports, PIDs
- Probe/USB status: check if Lauterbach hardware is connected
- Auto-register launched instance as MCP session

### Out of Scope
- Docker/container orchestration (existing t32_headless.shs covers this)
- Remote host launch (only localhost)
- Firmware flashing or probe firmware recovery
- T32 license management

## I/O Examples

### t32_launch
**Input:**
```json
{
  "architecture": "arm",
  "config": "config/t32/t32_stm_headless.t32",
  "headless": true,
  "port": 20000,
  "startup_script": "config/t32/stm32wb_native_start.cmm"
}
```
**Output (success):**
```json
{
  "status": "launched",
  "pid": 12345,
  "port": 20000,
  "session_id": "t32_20000",
  "headless": true,
  "message": "PowerView launched (headless, port 20000). Session auto-registered."
}
```
**Output (already running):**
```json
{
  "status": "already_running",
  "pid": 12345,
  "port": 20000,
  "message": "PowerView already running on port 20000. Use t32_session_open to connect."
}
```

### t32_shutdown
**Input:**
```json
{
  "port": 20000,
  "force": false
}
```
**Output:**
```json
{
  "status": "shutdown",
  "method": "graceful",
  "message": "PowerView on port 20000 terminated via QUIT command."
}
```

### t32_status
**Input:**
```json
{}
```
**Output:**
```json
{
  "installation": {
    "t32_dir": "/opt/t32",
    "binary": "/opt/t32/bin/pc_linux64/t32marm",
    "t32rem": "/opt/t32/bin/pc_linux64/t32rem",
    "version": "2024.09",
    "xvfb_available": true
  },
  "processes": [
    {"pid": 12345, "port": 20000, "arch": "arm", "uptime": "2h 15m"}
  ],
  "probe": {
    "usb_connected": true,
    "device": "/dev/lauterbach/trace32/powerdebug_ii"
  },
  "configs": [
    "config/t32/t32_stm_headless.t32",
    "config/t32/t32_rcl_only.t32"
  ]
}
```

## Acceptance Criteria

1. **AC-1:** `t32_launch` spawns PowerView as background process and returns PID
2. **AC-2:** `t32_launch` with `headless: true` uses xvfb-run automatically
3. **AC-3:** `t32_launch` waits for RCL port to become ready (polls with t32rem PING)
4. **AC-4:** `t32_launch` auto-registers the new instance as an MCP session
5. **AC-5:** `t32_launch` rejects if port already in use
6. **AC-6:** `t32_shutdown` sends QUIT via t32rem, waits for process exit
7. **AC-7:** `t32_shutdown` with `force: true` kills process if QUIT fails
8. **AC-8:** `t32_shutdown` cleans up MCP session and tracked PID
9. **AC-9:** `t32_status` discovers T32 installation directory and binaries
10. **AC-10:** `t32_status` lists running T32 processes with ports and PIDs
11. **AC-11:** `t32_status` checks USB probe connectivity
12. **AC-12:** `t32_status` lists available config files
13. **AC-13:** All three tools are registered in the MCP tools list
14. **AC-14:** Tools handle missing T32 installation gracefully (clear error)

## Dependencies
- `rt_process_run` / process spawning FFI (exists in `src/lib/nogc_sync_mut/io/process_ops.spl`)
- `t32rem` binary for health checks and QUIT command
- Existing session management in `session_tools.spl`
- Existing `t32find_backend()` for binary discovery

## Related Docs
- Plan: `doc/plan/t32_mcp_lifecycle.md`
- Design: `doc/design/t32_mcp_lifecycle.md`
- T32 Skill: `.claude/skills/t32.md`
- MCP Skill: `.claude/skills/mcp.md`
