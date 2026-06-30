# Dashboard UI Research: Inspiration for Simple Language LLM Dashboard

**Date:** 2026-04-06
**Purpose:** Web research on best developer/AI dashboard UIs for improving the Simple language LLM dashboard

---

## 1. Terminal TUI Dashboards (Developer Tools)

### K9s (Kubernetes TUI)
- **Layout:** Single-screen with header bar (context/namespace), main resource table, and command bar at bottom. Views switch entirely (pods, services, deployments) rather than splitting panels.
- **Key Components:** Color-coded resource tables with status columns (AGE, NAMESPACE, NAME, IP, NODE, STATUS). Inline search with `/`, command mode with `:`. Log viewer overlay.
- **Color Scheme:** Dark background, color-coded status states: green (new/ready), blue (modify), red (error), yellow (highlight), purple (kill), grey (completed). Supports custom skins with granular color control per element.
- **What Makes It Polished:** Vim-style navigation (j/k/h/l), breadcrumb showing current resource type and namespace, instant search filtering, hotkey help accessible with `?`, smooth view transitions. The single-view-at-a-time pattern prevents clutter.
- **Patterns Worth Copying:**
  - Command palette (`:` mode) for quick navigation between views
  - Color-coded status with semantic meaning (not decorative)
  - Breadcrumb trail showing navigation context
  - Hotkey overlay accessible anytime with `?`
  - Skin/theme system with per-element color control

### Lazygit (Git TUI)
- **Layout:** Six-panel split layout: Status (top-left), Files (mid-left), Branches (below), Commits (below), Stash (bottom-left), and a large Diff pane (right side ~60% width). Panels numbered 1-5 for quick switching.
- **Key Components:** Commit graph with author color-coding, line-level staging in diff view, optimistic rendering (UI updates before git commands finish), three screen modes (normal/half/full) via `+`/`_` cycling.
- **Color Scheme:** Dark with muted borders, bright highlight on active panel, commit graph uses distinct colors per author, diff view uses standard green/red for additions/deletions.
- **What Makes It Polished:** Panel focus system where active panel has bright border while inactive are dim. The diff panel on the right provides immediate context for whatever is selected on the left. Optimistic rendering makes staging feel instant. Enlarged window mode for commit graph gives deeper visibility when needed.
- **Patterns Worth Copying:**
  - Master-detail layout (selection on left, detail on right)
  - Panel numbering for instant focus switching (1/2/3/4/5)
  - Screen mode cycling (compact -> half -> full) for any panel
  - Active/inactive panel border dimming for clear focus indication
  - Optimistic rendering for perceived performance

### btop++ (System Monitor)
- **Layout:** Multi-zone dashboard: CPU graphs (top), Memory/Disk (middle), Network (middle-right), Process list (bottom ~40% of screen). Each zone has its own mini-header.
- **Key Components:** Braille-character graphs (Unicode U+2800-U+28FF) for high-resolution sparklines, per-core CPU bars, memory composition bars, network I/O graphs, sortable/filterable process table with tree view.
- **Color Scheme:** 24-bit truecolor with multiple built-in themes. Default uses gradient colors: CPU bars go from green (low) through yellow to red (high). Process list uses color to indicate CPU/memory intensity. Supports graceful degradation to 256-color and even TTY mode.
- **What Makes It Polished:** The Braille-pattern graphs are the signature feature -- they provide 2x4 resolution per character cell, creating smooth curves that look almost graphical. Mouse support for clicking buttons, scrolling lists. Game-inspired menu design for configuration. Theme compatibility with bpytop/bashtop community themes.
- **Patterns Worth Copying:**
  - Braille Unicode graphs (U+2800-U+28FF) for high-resolution mini-charts
  - Graceful degradation: braille -> block -> TTY symbols based on terminal capability
  - Gradient color bars for resource utilization (green->yellow->red)
  - Per-zone mini-headers with zone-specific stats
  - Full mouse support as complement to keyboard navigation
  - Community theme ecosystem

---

## 2. AI Agent Monitoring Dashboards

### LangSmith (LangChain)
- **Layout:** Main navigation sidebar (left), project list/dashboard (center), detail panel (right or overlay). Dashboard has two types: prebuilt (auto-generated per project) and custom (user-configurable chart collections).
- **Key Components:**
  - **Waterfall graph** for trace latency visualization -- shows timing of each component in a chain/agent execution as horizontal bars, nested by parent/child relationship
  - **Run Tree** model -- hierarchical tree where parent run = agent execution, child runs = tool calls, prompt formatting, LLM calls, output parsing
  - **Trace detail view** -- click any span to inspect inputs, outputs, tokens, timings
  - **Dashboard metrics** -- P50/P99 latency, error rates, token usage, cost breakdowns, feedback scores
  - **Status indicators** -- green checkmarks for success, red error icons for failures
- **Color Scheme:** Light/clean web UI with color-coded status (green=success, red=error), muted greys for metadata, blue for interactive elements.
- **What Makes It Polished:** The waterfall view is the killer feature -- it immediately shows where time is being spent in complex agent chains. The nested tree structure maps directly to the execution model, making debugging intuitive. Custom dashboards allow teams to build role-specific views.
- **Patterns Worth Copying:**
  - **Waterfall/Gantt-style trace timeline** -- horizontal bars showing span duration, nested by call depth
  - **Run Tree** with expandable nodes showing inputs/outputs per step
  - Prebuilt + custom dashboard duality (auto-generated defaults, user-customizable)
  - P50/P99 latency charts with cost breakdown
  - Click-through from summary -> trace -> span detail

### Langfuse (Open Source)
- **Layout:** Web UI with sidebar navigation, main content area with trace list, detail panel with nested observation tree.
- **Key Components:**
  - **Three-level data model:** Sessions > Traces > Observations (with subtypes: generations, tool calls, retrieval steps)
  - **Nested observation tree** -- hierarchical visualization of LLM call chains
  - **Session replay** -- group traces by user session for debugging multi-turn conversations
  - **Annotation queues** for human evaluation
  - **LLM-as-judge evaluations** with scoring
- **Color Scheme:** Clean, modern web UI. MIT-licensed open source.
- **What Makes It Polished:** The three-level hierarchy (session -> trace -> observation) maps perfectly to conversational AI. Each observation type has specific metadata (generations track tokens/model, retrievals track documents, tools track inputs/outputs).
- **Patterns Worth Copying:**
  - Session > Trace > Observation hierarchy for conversational AI
  - Observation type-specific metadata (different detail views for LLM calls vs tool calls vs retrieval)
  - Annotation queue workflow for human evaluation
  - Self-hostable with MIT license

### Arize Phoenix (Open Source)
- **Layout:** Web dashboard with project overview, trace list, trace detail with span tree, experiments section, playground.
- **Key Components:**
  - **Span-based trace viewer** built on OpenTelemetry standards
  - **Experiment recording indicator** -- pulsing red recording icon with elapsed timer (replaces boring loading spinner)
  - **Restyled UI components** with improved dark mode contrast, smoother transitions, cleaner hover/focus states
  - **Playground** for prompt optimization and model comparison
  - **Version-controlled datasets** for experimentation
- **Color Scheme:** Dark mode with improved contrast (recent redesign), semantic coloring for status.
- **What Makes It Polished:** Built on OpenTelemetry so traces are vendor/framework agnostic. The experiment recording indicator is a small but delightful detail -- pulsing red dot + timer makes running experiments feel alive. Dark mode was recently redesigned specifically for better contrast.
- **Patterns Worth Copying:**
  - Pulsing recording indicator with elapsed timer for long-running operations
  - OpenTelemetry-based trace model (vendor agnostic)
  - Prompt playground integrated directly into observability tool
  - Dark mode designed for contrast, not just color inversion

---

## 3. Multi-Agent AI TUI Dashboards (Newest Category)

### Gastown (Steve Yegge's Multi-Agent Workspace Manager)
- **Layout:** Three-panel TUI via `gt feed`:
  1. **Agent Tree** (left) -- hierarchical view of all agents grouped by rig and role
  2. **Convoy Panel** (center) -- in-progress and recently-landed convoys
  3. **Event Stream** (right) -- chronological feed of creates, completions, slings, nudges
- **Key Components:**
  - **Problems view** -- surfaces agents needing human intervention by analyzing structured data (critical at 20-50+ agents)
  - **Web dashboard** -- single-page overview of agents, convoys, hooks, queues, issues, escalations
  - Navigation: j/k scroll, Tab switch panels, 1/2/3 jump to panel, ? help, q quit
- **Color Scheme:** Terminal dark theme with status-coded agents.
- **What Makes It Polished:** The "Problems view" is the key innovation -- at scale, you can't watch an activity stream; you need a filtered view of "things that need attention." The three-panel layout (tree + status + stream) provides overview-to-detail navigation.
- **Patterns Worth Copying:**
  - **Problems/Attention view** -- filtered list of items needing human intervention
  - Agent grouping by rig/role in tree hierarchy
  - Three-panel: Tree | Status | Event Stream
  - Both TUI and web dashboard for same data (terminal for dev, web for team)

### Ralph TUI (AI Agent Loop Orchestrator)
- **Layout:** Task-centric dashboard with agent output area and control bar. Toggle between summary and detailed views with `d`.
- **Key Components:**
  - **Task list** with dependency-aware ordering and priority-based selection
  - **Subagent tracing** -- see nested agent calls in real-time
  - **Autonomous loop controls** -- Space to start, p to pause
  - **Bundled color themes:** bright, catppuccin, dracula, high-contrast, solarized-light
- **Color Scheme:** Multiple theme support including dark themes (dracula, catppuccin) and high-contrast for accessibility.
- **What Makes It Polished:** The task-first design means you always see what the agent is working on and what's next. Subagent tracing gives visibility into nested calls. Theme variety shows attention to personal preference.
- **Patterns Worth Copying:**
  - Task-centric view (what's being done, what's next, what's done)
  - Subagent trace tree for nested call visibility
  - Summary/detail toggle (press `d`)
  - Multiple built-in color themes (catppuccin, dracula, etc.)

### Sidecar (AI Agent Companion TUI)
- **Layout:** Designed as a side panel next to your coding agent. Typical setup: agent on left, sidecar on right. Can run two instances side-by-side for multi-view.
- **Key Components:**
  - **Files plugin** -- collapsible directory tree with live code preview, auto-refresh on changes
  - **Git integration** -- staged/modified/untracked files, diffs, stage/unstage
  - **Conversation browser** -- browse agent chat history with search and token totals
  - **Task monitoring** via td plugin
  - **Tab/Shift-Tab** for switching between plugins
- **Color Scheme:** Dark terminal with muted UI, focus highlights.
- **What Makes It Polished:** Mouse support on almost every element. Live file watching auto-refreshes views. The "plugin" architecture means each panel is a focused view that can be swapped. Running two instances for a dashboard setup is creative.
- **Patterns Worth Copying:**
  - Plugin architecture for swappable panel content
  - Full mouse support alongside keyboard shortcuts
  - Live file watching with auto-refresh
  - Conversation history browser with token count display
  - Companion layout (designed to sit beside another tool)

### OpenCode (AI Coding Agent TUI)
- **Layout:** Main chat area (center), sidebar with session metadata, LSP status, MCP status, todos, file diffs.
- **Key Components:**
  - **Slash command system** (`/` + command name)
  - **Session metadata** display
  - **LSP integration status** in sidebar
  - **MCP server status** in sidebar
  - **Todo list** integrated into sidebar
  - **Automatic dark/light detection** via terminal background luminance
- **Color Scheme:** Auto-detected dark/light mode with 1-second timeout fallback to dark. Multiple built-in themes. Built on Yoga layout system via @opentui rendering engine.
- **What Makes It Polished:** The sidebar combines all relevant context (LSP, MCP, todos, diffs) in one place. Automatic theme detection means zero configuration for most users. The Yoga-based layout engine ensures proper proportional sizing.
- **Patterns Worth Copying:**
  - Sidebar with multi-section status (LSP, MCP, session, todos)
  - Automatic dark/light theme detection
  - Yoga-based flexible layout for proportional panel sizing
  - Slash command system for quick actions

### Conduit (Multi-Agent TUI)
- **Layout:** Side-by-side view for running Claude Code and Codex CLI simultaneously.
- **Patterns Worth Copying:**
  - Side-by-side agent comparison view
  - Multi-agent orchestration from single terminal

### TmuxCC (AI Agent Dashboard for tmux)
- **Layout:** Centralized monitoring panel that scans tmux sessions/windows/panes for AI agents.
- **Key Components:**
  - **Agent detection** by process name, window title, command line
  - **Pane content analysis** for status and approval detection
  - **Keystroke sending** to panes for approvals/rejections
  - **Agent-specific parsers** for Claude Code, OpenCode, Codex CLI, Gemini CLI
  - **Configurable polling** interval and capture lines
- **Patterns Worth Copying:**
  - Auto-detection of agent processes across tmux panes
  - Agent-specific parsers for different tools
  - Remote approval/rejection via keystroke injection

---

## 4. Grafana (Observability Dashboard Design Patterns)

### Layout System
- **24-column grid** system for flexible panel arrangement
- **Z-pattern scanning**: key content in top-left, users scan left-to-right, top-to-bottom
- **Row-based organization**: general status at top, details at bottom
- **Spacing:** 20px margins between rows, 10px gaps between panels

### Visual Hierarchy Principles
- **Size = Importance**: Key metrics in large stat panels, supporting data in smaller panels beneath
- **Position = Priority**: Top-left corner gets most attention
- **Color = Status**: Semantic colors for thresholds (green/yellow/red)
- **Contrast = Focus**: Active elements brighter, supporting elements dimmer

### Panel Types (applicable to TUI)
- **Stat panels** -- single big number with optional sparkline
- **Gauge panels** -- visual meter for bounded values
- **Table panels** -- sortable, filterable data grids
- **Timeseries panels** -- line/area charts over time
- **Bar gauge** -- horizontal/vertical bars for comparisons

### What Makes Grafana Feel Professional
- Consistent spacing and alignment throughout
- Thresholds with color transitions (green -> amber -> red)
- Variable/template system for parameterized dashboards
- Dashboard linking for drill-down navigation
- Annotations overlaid on timeseries for context

---

## 5. Universal Design Patterns: Basic vs. Polished

### What Separates "Basic" from "Polished"

| Aspect | Basic | Polished |
|--------|-------|----------|
| **Color** | Random colors or all-white | Semantic colors (green=ok, red=error, yellow=warn, dim=metadata) |
| **Layout** | Fixed panels, no responsiveness | Flexible grid, panel resizing, screen mode cycling |
| **Navigation** | Mouse-only or basic arrow keys | Vim keys + number keys + command palette + breadcrumbs + search |
| **Information Density** | Either too sparse or too cluttered | Hierarchical: overview -> summary -> detail, with toggle between levels |
| **Status** | Text labels ("Running", "Error") | Color-coded indicators + icons + semantic styling |
| **Graphs** | ASCII art or absent | Braille Unicode (U+2800-U+28FF) or block elements with gradients |
| **Feedback** | Loading spinner | Pulsing recording indicator with elapsed timer, optimistic rendering |
| **Focus** | No visual distinction | Active panel bright border, inactive dimmed, breadcrumb context |
| **Theme** | Hardcoded colors | Multiple themes (dracula, catppuccin, etc.) + auto dark/light detection |
| **Help** | README | In-app `?` hotkey overlay showing all keybindings in context |
| **Mouse** | No support | Full mouse support as complement (not replacement) to keyboard |
| **Degradation** | Breaks on limited terminals | Graceful: truecolor -> 256-color -> 16-color -> TTY |

### Top 10 Concrete Improvements to Apply

1. **Waterfall trace timeline** (from LangSmith) -- horizontal bars showing LLM call duration, nested by call depth, immediately reveals bottlenecks
2. **Braille sparkline graphs** (from btop) -- use U+2800-U+28FF for high-resolution inline charts showing token usage, latency, cost over time
3. **Problems/Attention view** (from Gastown) -- filtered list of items needing human action, critical when monitoring multiple agents
4. **Master-detail layout** (from lazygit) -- selection list on left ~40%, detail panel on right ~60%, with active/inactive panel border dimming
5. **Command palette** (from k9s) -- `:` to enter command mode, `/` for search, `?` for help overlay
6. **Summary/Detail toggle** (from Ralph) -- press a key to cycle between compact overview and expanded detail
7. **Semantic color system** -- 80% default foreground, headers bold+accent, metadata dim, status semantic, interactive elements only get accent color
8. **Sidebar status sections** (from OpenCode) -- LSP status, MCP status, session info, token usage, all in compact sidebar sections
9. **Theme system with presets** (from Ralph/btop) -- ship catppuccin, dracula, high-contrast, solarized + auto-detection
10. **Gradient utilization bars** (from Grafana/btop) -- green->yellow->red bars for any percentage metric (context usage, token budget, latency budget)

---

## Sources

### Terminal TUI Dashboards
- [K9s Official](https://k9scli.io/)
- [K9s - The Powerful Terminal UI for Kubernetes](https://palark.com/blog/k9s-the-powerful-terminal-ui-for-kubernetes/)
- [Lazygit GitHub](https://github.com/jesseduffield/lazygit)
- [How to Use Lazygit](https://www.freecodecamp.org/news/how-to-use-lazygit-to-improve-your-git-workflow/)
- [btop GitHub](https://github.com/aristocratos/btop)
- [btop: True Color Charts and GPU Stats](https://www.x-cmd.com/install/btop/)
- [Awesome TUIs List](https://github.com/rothgar/awesome-tuis)
- [TUI Studio](https://tui.studio/)

### AI Agent Observability
- [LangSmith Observability](https://www.langchain.com/langsmith/observability)
- [LangSmith Waterfall Graphs](https://changelog.langchain.com/announcements/waterfall-graphs-to-spot-latency-bottlenecks-in-langsmith)
- [LangSmith Dashboards Docs](https://docs.langchain.com/langsmith/dashboards)
- [LangSmith Tracing Deep Dive](https://medium.com/@aviadr1/langsmith-tracing-deep-dive-beyond-the-docs-75016c91f747)
- [Langfuse Overview](https://langfuse.com/docs/observability/overview)
- [Langfuse GitHub](https://github.com/langfuse/langfuse)
- [Arize Phoenix](https://phoenix.arize.com/)
- [Phoenix GitHub](https://github.com/Arize-ai/phoenix)
- [15 AI Agent Observability Tools 2026](https://aimultiple.com/agentic-monitoring)

### Multi-Agent TUI Dashboards
- [Gastown GitHub](https://github.com/steveyegge/gastown)
- [Gastown: Multi-Agent Orchestration](https://www.wal.sh/research/gastown.html)
- [Ralph TUI](https://ralph-tui.com/)
- [Ralph TUI: Mission Control Dashboard](https://www.verdent.ai/guides/ralph-tui-ai-agent-dashboard)
- [Sidecar](https://sidecar.haplab.com/)
- [Sidecar GitHub](https://github.com/marcus/sidecar)
- [OpenCode TUI Docs](https://opencode.ai/docs/tui/)
- [OpenCode Themes](https://opencode.ai/docs/themes/)
- [Conduit](https://getconduit.sh/)
- [TmuxCC GitHub](https://github.com/nyanko3141592/tmuxcc)

### Grafana & Design Patterns
- [Grafana Dashboard Best Practices](https://grafana.com/docs/grafana/latest/visualizations/dashboards/build-dashboards/best-practices/)
- [Getting Started with Grafana Dashboard Design](https://grafana.com/blog/getting-started-with-grafana-best-practices-to-design-your-first-dashboard/)
- [7 Best Practices for Grafana Dashboard Design](https://www.metricfire.com/blog/7-best-practices-for-grafana-dashboard-design/)
- [TUI Design Patterns](https://lobehub.com/skills/neversight-learn-skills.dev-tui-design)
- [TUI Design System (Figma)](https://www.figma.com/community/file/1605441651613376418/tui-design-system-terminal-user-interface-components-v0-1)
- [Monitoring Tools Comparison](https://www.blackmoreops.com/top-atop-btop-htop-linux-monitoring-tools-comparison/)
