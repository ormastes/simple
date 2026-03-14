# TUI Tools for LLM/Agent Control Interfaces — Research Report

**Date:** 2026-03-14
**Scope:** Web research on TUI dashboard tools, LLM/agent TUIs, TUI frameworks, and UX patterns

---

## 1. System Monitoring TUIs — Established Patterns

### Key Tools

| Tool | Language | Framework | Key UX Pattern |
|------|----------|-----------|----------------|
| **btop/btop++** | C++ | Custom | Multi-panel: CPU bars, memory, disk, network, process list — all visible simultaneously |
| **htop** | C | ncurses | Horizontal meter bars + scrollable process list; color-coded CPU columns |
| **glances** | Python | curses | Modular widgets; client/server mode; web UI fallback; plugin architecture |
| **xtop** | Rust | ratatui | btop clone in Rust; demonstrates ratatui's viability for complex dashboards |

### UX Patterns Observed
- **Always-visible multi-pane layout**: CPU, memory, disk, network stats all rendered simultaneously — no tab switching for core metrics
- **Bar/sparkline widgets**: Real-time data shown as horizontal bar graphs and sparklines
- **Color-coded severity**: Green/yellow/red thresholds for resource usage
- **Keyboard-driven navigation**: Arrow keys to select, enter to drill down, single-letter hotkeys
- **Polling interval**: Configurable refresh rates (1-5s typical)
- **Responsive layout**: Panels reflow based on terminal size

---

## 2. Git/Docker/K8s TUIs — "Lazy" Pattern

### Key Tools

| Tool | Language | Framework | Domain |
|------|----------|-----------|--------|
| **lazygit** | Go | gocui | Git operations |
| **lazydocker** | Go | gocui | Docker container management |
| **k9s** | Go | tview | Kubernetes cluster management |
| **lazyrestic** | Rust | ratatui | Backup management |

### UX Patterns Observed
- **Left list + right detail pane**: Master-detail layout is the dominant pattern. Left panel shows a list of items (containers, branches, pods), right panel shows details/logs for the selected item
- **Modal keybinding layers**: Context-sensitive keybindings that change based on which pane is focused. A status bar shows available keys
- **Real-time log streaming**: Log panes that auto-scroll with new output, with ability to pause/search
- **Inline actions with confirmation**: Delete, restart, force-push all happen inline with a confirmation prompt
- **Multi-pane always-onscreen**: Unlike modal web UIs, TUIs keep multiple contexts visible simultaneously — "having a couple different panes always-onscreen with some dedicated different bits of context in them feels sharp/smart"
- **Command palette / fuzzy finder**: Quick navigation via fuzzy search (k9s uses this extensively)

---

## 3. Tmux Session Managers

### Key Tools

| Tool | Language | Config Format | Approach |
|------|----------|---------------|----------|
| **tmuxinator** | Ruby | YAML | Declarative session configs |
| **tmuxp** | Python | YAML/JSON | libtmux-based, session freeze/restore |
| **smug** | Go | YAML | Lightweight, inspired by tmuxinator |
| **tmux-wizard-tui** | Rust | — | Popup integration, adaptive UI |
| **tmux-tui** | Rust | — | TUI for session management |

### Integration Patterns
- **Declarative YAML configs**: Define windows, panes, commands, and layouts in config files; reproduce environments with one command
- **Popup mode**: Use tmux's floating popup windows (`-E` flag) to launch TUI session managers inside tmux itself
- **Session freeze/restore**: Capture current tmux state and serialize to config for reproducibility
- **Adaptive UI**: Compact mode for popups vs. full mode for standalone terminal

---

## 4. LLM/Agent TUI Tools — The 2025-2026 Ecosystem

This is the most rapidly evolving category. Multiple tools have emerged specifically for managing AI coding agent sessions.

### 4.1 Agent Session Managers

| Tool | Language | Framework | Agent Support | Key Feature |
|------|----------|-----------|---------------|-------------|
| **claude-squad** | Go | bubbletea | Claude, Codex, OpenCode, Amp | Git worktree isolation per agent |
| **Agent of Empires** | Rust | ratatui | Claude, OpenCode, Mistral, Gemini, Codex, Copilot, Pi.dev | Docker sandboxing, status detection |
| **Agent Hand** | Rust | ratatui | Claude, Gemini | Sub-50ms launch, tmux integration |
| **agtx** | Go | bubbletea | Claude, Codex, Gemini | Multi-project dashboard, auto agent switching |
| **IttyBitty** | — | tmux-based | Claude Code | Hierarchical spawning (agents spawn sub-agents) |
| **TmuxCC** | — | — | Claude, OpenCode, Codex, Gemini | Centralized tmux pane monitoring |
| **claude-orchestra** | — | — | Claude Code | Session monitoring + Telegram bot |
| **ATM (Agent Tmux Monitor)** | Rust | ratatui | Claude Code | Context usage tracking, cost tracking |

### UX Patterns Observed

**Common Layout:**
```
┌─────────────────────────────────────────────┐
│  Agent List / Status Bar                     │
├──────────────────────┬──────────────────────┤
│                      │                      │
│  Agent Terminal      │  Agent Log /         │
│  (live session)      │  Status Details      │
│                      │                      │
├──────────────────────┴──────────────────────┤
│  Key Commands / Status Line                  │
└─────────────────────────────────────────────┘
```

- **Agent status detection**: Polling tmux panes every 2s to determine agent state (running, waiting for input, idle, error)
- **Git worktree isolation**: Each agent gets its own worktree to prevent merge conflicts
- **Docker sandboxing**: Optional container isolation for untrusted agent operations
- **Cost tracking**: Real-time display of token usage and API costs per session
- **Context window monitoring**: Visual indicator of how much context each agent has consumed
- **Session persistence**: Resume interrupted work with automatic state saving

### 4.2 Agent Loop Orchestrators

| Tool | Key Innovation |
|------|----------------|
| **Ralph TUI** | Full task-driven orchestration: task tracker plugins (JSON PRD, Beads) + agent adapters (Claude, OpenCode, Droid) + autonomous loop with error recovery |
| **Operator** | Kanban-shaped queue management with priority-based work assignment |
| **Overstory** | Inter-agent messaging via SQLite mail system |

**Ralph TUI Architecture (most mature):**
- **Three-layer architecture**: Task Trackers → Orchestration Engine → Agent Adapters
- **Plugin system**: Registry-based factory pattern for extensibility
- **Template engine**: Handlebars templates with context injection for agent prompts
- **Task graph**: Automatic dependency resolution and parallel execution scheduling
- **State persistence**: Resume interrupted work seamlessly
- **"Overnight development" pattern**: Define tasks, let agents work through backlog autonomously

### 4.3 Native Claude Code Agent Teams
- Built-in to Claude Code itself (not a separate TUI)
- One session acts as team lead, coordinates and assigns tasks
- Teammates work independently in their own context windows
- Automatic dependency unblocking when prerequisites complete
- Communication via inter-agent messaging

---

## 5. TUI Frameworks — Architectural Comparison

### Framework Matrix

| Framework | Language | Architecture | Performance | Best For |
|-----------|----------|-------------|-------------|----------|
| **ratatui** | Rust | Unopinionated library; you own the event loop | 30-40% less memory, 15% less CPU vs bubbletea | Complex, performance-critical dashboards |
| **bubbletea** | Go | Elm Architecture (TEA); framework owns the loop | Good, but GC overhead | Rapid prototyping, standard CLIs |
| **textual** | Python | Full framework; manages app lifecycle | Slower but acceptable | Rich widget sets, web-like layouts |
| **blessed/blessed-contrib** | Node.js | DOM-like API; widget-based | Moderate | Dashboard-style UIs with graphs |

### Core Architectural Patterns

#### The Elm Architecture (TEA) — Used by BubbleTea
```
Model → View → [User Input] → Update → Model → View → ...
```
- **Model**: Application state (all data)
- **Update**: Pure function: `(Model, Message) → Model`
- **View**: Pure function: `Model → UI`
- Predictable, testable, but less flexible

#### Immediate Mode Rendering — Used by Ratatui
```
while running:
    state = process_events(state)
    draw_ui(state)  # redraw everything from scratch
```
- You own the loop; full control
- Redraw entire UI every frame based on current state
- Framework handles diff-based rendering under the hood

#### Double Buffer + Diff Rendering — Universal Pattern
- Render to offscreen buffer
- Diff against previous frame
- Only emit terminal escape codes for changed cells
- Ratatui, blessed, and textual all use this technique
- Sub-millisecond rendering even with complex layouts

#### Layout System
- **Constraint-based**: Length, Min, Max, Ratio, Percentage (ratatui)
- **Grid-based**: Rows/columns with span support (blessed-contrib)
- **Flex-based**: CSS-like flexbox (textual)

### Key Rendering Features
- **Mode 2026**: BubbleTea v2 supports synchronized output specification to eliminate screen tearing in modern terminals (Ghostty, etc.)
- **Smart cursor movement**: Minimize cursor repositioning commands
- **Screen damage buffer**: Track which cells actually changed
- **Zero-copy widgets**: Render widgets without consuming them (ratatui reference pattern)

---

## 6. Patterns Relevant to a Custom Language TUI

### What a Simple-language TUI Framework Would Need

Based on the research, the essential abstractions are:

1. **Terminal abstraction layer**
   - Raw mode enter/exit
   - ANSI escape code generation (cursor, color, style)
   - Mouse event capture
   - Terminal size detection and resize events
   - Alternate screen buffer

2. **Rendering engine**
   - Cell buffer (2D grid of styled characters)
   - Double buffering with diff computation
   - Constraint-based layout solver (split screen into rectangles)

3. **Widget protocol**
   - `render(area: Rect, buffer: Buffer)` interface
   - Built-in widgets: text, paragraph, list, table, gauge/bar, sparkline, tabs, block (border+title)
   - Composable: widgets contain widgets

4. **Event loop**
   - Poll for terminal events (key, mouse, resize)
   - Timer/tick events for periodic refresh
   - Async event sources (process output, network)

5. **State management**
   - Either TEA pattern (framework-driven) or immediate mode (user-driven)
   - For a compiler/agent dashboard, immediate mode is likely better (more control)

### Feature Priorities for an Agent Dashboard

From the surveyed tools, these features appear in order of importance:

| Priority | Feature | Seen In |
|----------|---------|---------|
| P0 | Multi-pane layout with agent list + detail view | All agent TUIs |
| P0 | Real-time agent status detection | claude-squad, Agent of Empires, ATM |
| P0 | Live terminal output streaming | IttyBitty, agtx |
| P1 | Keyboard-driven navigation with context-sensitive keys | lazygit, k9s |
| P1 | Agent spawn/stop/restart controls | All agent TUIs |
| P1 | Log viewing with scroll/search | lazydocker, k9s |
| P2 | Cost/token tracking | ATM, claude-orchestra |
| P2 | Task queue with priority assignment | Ralph TUI, Operator |
| P2 | Git worktree isolation per agent | claude-squad, Agent of Empires |
| P3 | Inter-agent messaging | Overstory (SQLite mail), Claude native teams |
| P3 | Template-driven prompt generation | Ralph TUI |
| P3 | Notification system (desktop/Telegram) | claude-orchestra |

---

## 7. Summary of Architectural Archetypes

### Archetype A: Session Monitor (ATM, claude-orchestra, TmuxCC)
- Watches existing tmux sessions
- Read-only dashboard with status polling
- Lightweight; no process management
- Good starting point

### Archetype B: Session Manager (claude-squad, Agent of Empires, Agent Hand)
- Creates and manages tmux sessions
- Git worktree provisioning
- Agent lifecycle management (spawn, stop, restart)
- Status detection and live output viewing

### Archetype C: Task Orchestrator (Ralph TUI, Operator)
- Full task queue management
- Autonomous agent loop (select task → execute → verify → next)
- Plugin architecture for agents and task trackers
- State persistence and error recovery
- Most complex but most powerful

### Archetype D: System Monitor (btop, htop, glances)
- Real-time system metrics
- Bar/sparkline/gauge widgets
- Polling-based data refresh
- Pure visualization, no process control

A comprehensive agent control TUI would combine elements of B + C + D: manage agent sessions, orchestrate task queues, and display real-time system/agent metrics.

---

## Sources

### System Monitoring TUIs
- [awesome-tuis — curated list](https://github.com/rothgar/awesome-tuis)
- [btop review — Both.org](https://www.both.org/?p=9668)
- [Terminal Trove — Monitoring Tools](https://terminaltrove.com/categories/monitoring/)
- [Glances — GitHub](https://github.com/nicolargo/glances)
- [Top 10 Linux Console Monitors — Jeff Geerling](https://www.jeffgeerling.com/blog/2025/top-10-ways-monitor-linux-console/)

### Git/Docker/K8s TUIs
- [lazydocker — GitHub](https://github.com/jesseduffield/lazydocker)
- [lazygit — via ITNEXT](https://itnext.io/essential-cli-tui-tools-for-developers-7e78f0cd27db)
- [lazyarchon — task management TUI](https://github.com/yousfisaad/lazyarchon)

### LLM/Agent TUIs
- [Ralph TUI — official site](https://ralph-tui.com/)
- [Ralph TUI — Peerlist article](https://peerlist.io/leonardo_zanobi/articles/ralph-tui-ai-agent-orchestration-that-actually-works)
- [Ralph TUI — DeepWiki architecture](https://deepwiki.com/subsy/ralph-tui)
- [Ralph TUI — Verdent guide](https://www.verdent.ai/guides/ralph-tui-ai-agent-dashboard)
- [claude-squad — GitHub](https://github.com/smtg-ai/claude-squad)
- [Agent of Empires — GitHub](https://github.com/njbrake/agent-of-empires)
- [IttyBitty — Adam Wulf blog](https://adamwulf.me/2026/01/itty-bitty-ai-agent-orchestrator/)
- [claude-orchestra — GitHub](https://github.com/jbduarte/claude-orchestra)
- [agtx — GitHub](https://github.com/fynnfluegge/agtx)
- [Operator — GitHub](https://github.com/untra/operator)
- [TmuxCC — GitHub](https://github.com/nyanko3141592/tmuxcc)
- [ATM (Agent Tmux Monitor) — crates.io](https://crates.io/crates/atm-tui)
- [Agent Hand — AI Tools Space](https://www.aitoolsspace.com/en/tools/agent-hand)
- [Overstory — GitHub](https://github.com/jayminwest/overstory)
- [OrKa — DEV Community](https://dev.to/marcosomma/real-time-cognition-building-an-observable-tui-for-ai-memory-in-orka-47d4)
- [agent-tui — GitHub](https://github.com/pproenca/agent-tui)

### TUI Frameworks
- [BubbleTea vs Ratatui — glukhov.org](https://www.glukhov.org/post/2026/02/tui-frameworks-bubbletea-go-vs-ratatui-rust/)
- [BubbleTea vs Ratatui — DEV Community](https://dev.to/dev-tngsh/go-vs-rust-for-tui-development-a-deep-dive-into-bubbletea-and-ratatui-2b7)
- [Ratatui layout docs](https://ratatui.rs/concepts/layout/)
- [Ratatui rendering docs](https://ratatui.rs/concepts/rendering/)
- [Ratatui widget docs](https://ratatui.rs/concepts/widgets/)
- [Ratatui TEA pattern](https://ratatui.rs/concepts/application-patterns/the-elm-architecture/)
- [blessed — GitHub](https://github.com/chjj/blessed)
- [blessed-contrib — GitHub](https://github.com/yaronn/blessed-contrib)
- [7 TUI Libraries — LogRocket](https://blog.logrocket.com/7-tui-libraries-interactive-terminal-apps/)
- [FrankenTUI — GitHub](https://github.com/Dicklesworthstone/frankentui)
- [TUI Framework Rankings — OSS Insight](https://ossinsight.io/collections/tui-framework/)

### Tmux Session Managers
- [tmuxinator — GitHub](https://github.com/tmuxinator/tmuxinator)
- [tmuxp — GitHub](https://github.com/tmux-python/tmuxp)
- [smug — GitHub](https://github.com/ivaaaan/smug)
- [tmux-wizard-tui — GitHub](https://github.com/williavs/tmux-wizard-tui)

### Claude Code Agent Teams
- [Claude Code Agent Teams — official docs](https://code.claude.com/docs/en/agent-teams)
- [Claude Code multi-agent guide — eesel.ai](https://www.eesel.ai/blog/claude-code-multiple-agent-systems-complete-2026-guide)
