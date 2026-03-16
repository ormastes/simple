# T32 MCP Lifecycle — Plan

## Objective
Add 3 lifecycle management tools to the T32 MCP server (26 total): `t32_launch`, `t32_shutdown`, `t32_status`.

## Current Status
| Component | Status | Evidence |
|-----------|--------|----------|
| T32 MCP Server | Real | 23 tools functional, protocol.spl |
| Session management | Real | session_open/close/resume in session_tools.spl |
| Backend detection | Real | t32rem + python bridge in session_tools.spl |
| Process spawning | Missing | No PowerView launch capability |
| Process shutdown | Missing | No graceful termination |
| Installation discovery | Missing | No status/discovery tool |

## What To Do
1. Create `lifecycle_tools.spl` with 3 tool handlers + process tracking state (difficulty: 3)
2. Add 3 tool schemas to `protocol.spl` (difficulty: 1)
3. Add 3 dispatch entries to `action_tools.spl` (difficulty: 1)
4. Wire import in `main.spl`, update tool count (difficulty: 1)

## Design
- **New file:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl`
- **State:** `McpT32Launched` class tracks PID/port/arch/config per launched instance
- **t32_launch:** Find binary → check port → spawn (xvfb-run if headless) → poll PING → auto-register session
- **t32_shutdown:** QUIT via t32rem → wait → force kill if requested → clean up session
- **t32_status:** Scan install dir, pgrep processes, check /dev/lauterbach/, list configs

## Related
- Requirement: `doc/requirement/t32_mcp_lifecycle.md`
- T32 Skill: `.claude/skills/t32.md`
