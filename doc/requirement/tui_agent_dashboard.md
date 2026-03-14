# TUI Agent Dashboard — Requirements

**Feature:** `tui_agent_dashboard`
**Date:** 2026-03-14
**Status:** Draft — awaiting user approval

**Related docs:**
- Research: `doc/research/tui_agent_dashboard_research.md`
- Plan: `doc/plan/tui_agent_dashboard.md` (Phase 4)
- Design: `doc/design/tui_agent_dashboard.md` (Phase 4)
- Tests: `test/system/tui_agent_dashboard_spec.spl` (Phase 6)

---

## Motivation

Developers running multiple Claude Code agents in parallel (via jj worktrees, tmux sessions, or agent loops) lack a unified view of:
- **System resources** — Is the machine overloaded? Is GPU being utilized?
- **VCS state** — Which worktrees exist? What branches are active?
- **Agent sessions** — Which agents are running? What are they doing?

A single TUI dashboard solves this by providing real-time monitoring and management from one terminal.

---

## Scope

### In Scope (v1 — Resource Status)

| ID | Feature | Description |
|----|---------|-------------|
| REQ-01 | CPU load | Display total CPU usage % (1s refresh) |
| REQ-02 | Memory load | Display used/total RAM in MB/GB |
| REQ-03 | CUDA/GPU load | Display GPU utilization % and VRAM usage (nvidia-smi) |
| REQ-04 | jj worktree list | Show all jj workspaces with their paths and current change |
| REQ-05 | Local branch list | Show jj/git bookmarks with push status |
| REQ-06 | Agent sessions | List active agent loop sessions (from `.build/agent_loop/`) |
| REQ-07 | tmux session list | Discover and display tmux sessions/windows |
| REQ-08 | Keyboard navigation | Arrow keys, tab between panels, q to quit |
| REQ-09 | Auto-refresh | Polling-based refresh (configurable interval, default 2s) |
| REQ-10 | Graceful shutdown | SIGINT/SIGTERM cleanup, restore terminal state |

### Out of Scope (v1)

- Agent spawning/killing from TUI (v2)
- tmux pane attach/detach (v2)
- Build/test triggering (v2)
- Cost tracking per agent (v2)
- Remote machine monitoring (v2)
- Web dashboard integration (v2)

---

## I/O Examples

### Example 1: Basic dashboard layout

```
┌─ System Resources ─────────────────────────────────────────────┐
│ CPU:  ████████░░░░░░░░  52%  (8 cores)                        │
│ MEM:  ██████████░░░░░░  63%  (10.1 / 16.0 GB)                 │
│ GPU:  ████░░░░░░░░░░░░  25%  (2.1 / 8.0 GB VRAM)  RTX 3070   │
└────────────────────────────────────────────────────────────────┘
┌─ JJ Worktrees ──────────────────┐ ┌─ Branches ────────────────┐
│ default   ~/dev/simple  @main   │ │ main       ✓ pushed       │
│ feat-tui  ~/dev/simple2 @tui    │ │ feat-tui   ⬆ 3 ahead     │
│ fix-bug   ~/dev/simple3 @fix    │ │ fix-bug    ⬆ 1 ahead     │
└─────────────────────────────────┘ └────────────────────────────┘
┌─ Agent Sessions ────────────────┐ ┌─ tmux Sessions ────────────┐
│ loop-001  running  iter:12      │ │ agent-1  3 windows  active │
│ loop-002  paused   iter:5       │ │ agent-2  1 window   idle   │
│ loop-003  done     iter:20      │ │ dev      2 windows  active │
└─────────────────────────────────┘ └─────────────────────────────┘
 [q]uit  [r]efresh  [↑↓]navigate  [tab]panel  [enter]details
```

### Example 2: No GPU available

```
┌─ System Resources ─────────────────────────────────────────────┐
│ CPU:  ████████░░░░░░░░  52%  (8 cores)                        │
│ MEM:  ██████████░░░░░░  63%  (10.1 / 16.0 GB)                 │
│ GPU:  (not available)                                          │
└────────────────────────────────────────────────────────────────┘
```

### Example 3: No agents running

```
┌─ Agent Sessions ────────────────┐
│ (no active agent loops)         │
└─────────────────────────────────┘
```

### Example 4: Terminal too narrow (graceful degradation)

```
┌─ System ──────────────────┐
│ CPU: 52%  MEM: 63%        │
│ GPU: 25%                  │
└───────────────────────────┘
┌─ Worktrees ───────────────┐
│ default  @main            │
│ feat-tui @tui             │
└───────────────────────────┘
```

### Example 5: CLI invocation

```bash
bin/simple tui                    # Launch dashboard (default 2s refresh)
bin/simple tui --refresh=5        # 5 second refresh interval
bin/simple tui --no-gpu           # Skip GPU detection
bin/simple tui --panels=resources,agents  # Show only specific panels
```

---

## Acceptance Criteria

1. `bin/simple tui` launches a full-screen terminal dashboard
2. Dashboard renders without flickering (double-buffer or cursor-home strategy)
3. CPU and memory stats update every refresh cycle
4. GPU stats shown when nvidia-smi is available, gracefully hidden otherwise
5. jj workspace list matches output of `jj workspace list`
6. Branch list matches output of `jj bookmark list`
7. Agent sessions discovered from `.build/agent_loop/` state files
8. tmux sessions discovered from `tmux list-sessions`
9. Keyboard: q quits, arrows navigate, tab switches panels
10. Terminal state fully restored on exit (cursor visible, normal mode)
11. Works in terminals >= 80x24

---

## Dependencies

| Module | Purpose | Status |
|--------|---------|--------|
| `dashboard.render/colors` | ANSI color codes | Exists |
| `dashboard.render/progress` | Progress bar rendering | Exists |
| `dashboard.render/table` | Table rendering | Exists |
| `cli/formatting` | Text padding/alignment | Exists |
| `io/process_ops` | Process execution (shell commands) | Exists |
| `io/signal_handlers` | SIGINT/SIGTERM handling | Exists |
| `io/sysinfo_ops` | Hostname, PID | Exists |
| `io/pipe` | Stdin/Stdout read/write | Exists |
| **NEW: `io/terminal`** | Raw mode, cursor control, key events | To build |
| **NEW: `tui/`** | Layout engine, widget system, render loop | To build |

---

## Architecture Notes

- **Pure polling** — no threads, no async. Single main loop reads input + refreshes display.
- **ANSI escape sequences** — direct terminal control, no ncurses dependency.
- **Data collection via shell** — `top -bn1`, `free`, `nvidia-smi`, `jj workspace list`, `tmux list-sessions` parsed as text.
- **Existing `daemon_sdk`** polling model fits perfectly for the refresh loop.
