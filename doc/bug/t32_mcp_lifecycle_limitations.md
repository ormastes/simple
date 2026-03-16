# T32 MCP Lifecycle — Limitations

## Limitation: t32_launch poll timeout too short for slow T32 startups
**Severity:** Medium
**Workaround:** Re-run `t32_session_open` manually after T32 finishes starting. The tool returns `status: "launched_not_ready"` when the 15-second window expires; the process is still running.
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:162` (polls `while polls < 30` at 500ms intervals = 15s max)

## Limitation: t32_launch PID may be xvfb-run wrapper, not the T32 process
**Severity:** Medium
**Workaround:** Use `t32_status` to confirm the actual running T32 PID via `pgrep`. When force-killing after a failed shutdown, use the PID from `pgrep` output rather than relying on the tracked PID.
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:136` (`nohup xvfb-run -a ... & echo $!` — `$!` is the shell background PID of `xvfb-run`, not the inner `t32marm` process)

## Limitation: t32_shutdown without force cannot terminate a hung T32 instance
**Severity:** High
**Workaround:** Call `t32_shutdown` with `force: true`. This sends SIGTERM then SIGKILL to the tracked PID. If the instance was not launched by this MCP server, manual `kill` is required (see limitation below).
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:256` (graceful path only runs `t32rem ... QUIT`; no fallback without `force`)

## Limitation: t32_shutdown force kill only works for MCP-launched instances
**Severity:** Medium
**Workaround:** For externally launched T32 instances, obtain the PID from `t32_status` (processes list) and kill manually with `kill -9 <pid>`.
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:269` (kill path guarded by `found_tracked` — only set for processes in `MCP_T32_LAUNCHED`)

## Limitation: t32_status probe detection requires udev symlinks from host setup script
**Severity:** Low
**Workaround:** Run `scripts/t32_host_setup.shs` on the host once to install the udev rules that create `/dev/lauterbach/trace32/` symlinks. Without this, `probe.usb_connected` will always report `false` even if hardware is physically connected.
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:442` (checks `ls /dev/lauterbach/trace32/`)

## Limitation: t32_status may miss T32 instances with non-standard binary names
**Severity:** Low
**Workaround:** Use `ps aux | grep t32` manually to find processes launched under non-standard binary names or wrappers. The `pgrep -a 't32m'` pattern only matches binaries whose name starts with `t32m` (e.g., `t32marm`, `t32marm64`, `t32mtc`).
**Related:** `examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl:389` (`pgrep -a 't32m'`)
