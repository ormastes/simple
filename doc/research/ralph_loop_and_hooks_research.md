# Research: Ralph Wiggum Loop, Claude Code Hooks, Codex CLI, and Agent Loop Patterns

**Date:** 2026-03-14

---

## 1. Ralph Wiggum Technique / Ralph Loop

### What It Is
The Ralph Wiggum technique, invented by Geoffrey Huntley, is an autonomous AI development loop pattern. Named after The Simpsons character, it embodies "persistent iteration despite setbacks." In its purest form, Ralph is a bash `while true` loop that repeatedly feeds an AI agent the same prompt file until the task is complete.

- **Original blog post:** https://ghuntley.com/ralph/
- **How-to repo:** https://github.com/ghuntley/how-to-ralph-wiggum
- **Inventor interview:** https://devinterrupted.substack.com/p/inventing-the-ralph-wiggum-loop-creator

### How It Works

**Original Bash Loop (external wrapper):**
```bash
while true; do
  claude --prompt PROMPT.md --print  # or similar invocation
  # agent reads IMPLEMENTATION_PLAN.md from disk
  # agent modifies code, updates plan, commits
  # loop restarts with fresh context but changed codebase
done
```

Key insight: The `IMPLEMENTATION_PLAN.md` file persists on disk between iterations and acts as shared state. Each iteration starts with fresh LLM context but reads the current codebase state. The agent figures out what to do next by reading the plan file each time. This solves context window accumulation.

**Claude Code Stop Hook Implementation (plugin):**
The official Claude Code plugin (`plugins/ralph-wiggum/`) uses a Stop hook instead of an external bash loop:
1. Claude works on the task
2. Claude finishes and tries to stop
3. The Stop hook intercepts the exit, returns `{"decision": "block", "reason": "..."}`
4. The reason tells Claude to re-read the prompt and continue
5. Repeats until `--max-iterations` is reached or task is complete

- **Official plugin:** https://github.com/anthropics/claude-code/tree/main/plugins/ralph-wiggum
- **Plugin README:** https://github.com/anthropics/claude-code/blob/main/plugins/ralph-wiggum/README.md

### Variants and Ecosystem

| Project | URL | Approach |
|---------|-----|----------|
| **Official plugin** | https://github.com/anthropics/claude-code/tree/main/plugins/ralph-wiggum | Stop hook in Claude Code |
| **Open Ralph Wiggum** | https://github.com/Th0rgal/open-ralph-wiggum | Multi-agent CLI wrapper (Claude Code, Codex, Copilot, OpenCode) — no plugins needed |
| **Ralph Orchestrator** | https://github.com/mikeyobrien/ralph-orchestrator | Hat-based multi-agent framework with typed events, backpressure gates, memory |
| **snarktank/ralph** | https://github.com/snarktank/ralph | Autonomous loop until PRD items complete |
| **Vercel ralph-loop-agent** | https://github.com/vercel-labs/ralph-loop-agent | Ralph loop for AI SDK |
| **Goose Ralph Loop** | https://block.github.io/goose/docs/tutorials/ralph-loop/ | Ralph pattern for Goose agent |

### Ralph Orchestrator Deep Dive
Ralph Orchestrator (mikeyobrien) adds structure on top of the basic loop:
- **Hat-based system:** Different "hats" (personas) trigger on events — e.g., planner hat triggers on `task.start` → publishes `plan.ready`, builder hat triggers on `plan.ready` → publishes `build.done`
- **Components:** `ralph-cli` (entry point), `ralph-core` (orchestration, event loop, hats, memories, tasks), `ralph-adapters` (backends for Claude, Kiro, Gemini, Codex)
- **Backpressure gates:** Quality enforcement between iterations
- **File-based state:** All state persists on disk, agents are stateless between iterations
- https://mikeyobrien.github.io/ralph-orchestrator/

### Safety Mechanisms
- `--max-iterations` flag (primary safety net)
- Ctrl+C to stop the loop
- `git reset --hard` to revert uncommitted changes
- Regenerate plan if trajectory goes wrong
- Each iteration commits, so you can inspect/revert individual steps

---

## 2. Claude Code Hooks System

### Overview
Hooks are user-defined commands that execute automatically at specific points in Claude Code's lifecycle. They provide **deterministic** control (always happens) vs relying on the LLM to choose.

- **Official docs:** https://code.claude.com/docs/en/hooks
- **Guide:** https://code.claude.com/docs/en/hooks-guide
- **Blog:** https://claude.com/blog/how-to-configure-hooks

### All 12 Lifecycle Events

| Event | When It Fires | Can Block? |
|-------|--------------|------------|
| **PreToolUse** | Before tool execution | Yes (deny/allow/ask) |
| **PostToolUse** | After successful tool execution | No |
| **PostToolUseFailure** | After failed tool execution | No |
| **UserPromptSubmit** | When user submits a prompt | No |
| **PermissionRequest** | When Claude requests permission | No |
| **Stop** | When Claude finishes responding | Yes (block) |
| **SubagentStop** | When a subagent finishes | Yes (block) |
| **SessionStart** | When session begins | No |
| **SessionEnd** | When session terminates | No |
| **Setup** | Via --init, --init-only, --maintenance flags | No |
| **Notification** | When Claude sends notifications | No |
| **PreCompact** | Before context compaction | No |

### Handler Types

| Type | Description | Use Case |
|------|-------------|----------|
| **Command** | Executes shell commands | Straightforward checks, formatting, linting |
| **Prompt** | Sends a prompt to a Claude model (single-turn, uses `$ARGUMENTS`) | Semantic evaluation, content analysis |
| **Agent** | Spawns subagents with tool access (Read, Grep, Glob) | Deep analysis requiring file exploration |

### Hook Output Formats

**PreToolUse (the only hook that can approve/deny):**
```json
{
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "deny",
    "permissionDecisionReason": "Destructive command blocked"
  }
}
```
- `"allow"` — proceed without showing permission prompt
- `"deny"` — cancel tool call, reason fed back to Claude
- `"ask"` — show permission prompt to user

**Stop hook (can block exit):**
```json
{
  "decision": "block",
  "reason": "Re-read PROMPT.md and continue working on remaining tasks"
}
```
- Exit code 2 from a hook command = blocking error (stderr becomes error message)

### Configuration Location
- `~/.claude/settings.json` — user-level (all projects)
- `.claude/settings.json` — project-level (version controlled)

### Async Hooks
Released January 2026. Run in the background without blocking Claude's execution. Useful for logging, notifications, telemetry.

---

## 3. OpenAI Codex CLI Extensibility

### Hooks (Experimental, March 2026)
Codex CLI added an **experimental hooks engine** with two events:
- **SessionStart** — executes when a session begins
- **Stop** — executes when a turn ends

Both support commands, status messages, and timeout configuration.

- **Changelog:** https://developers.openai.com/codex/changelog/
- **Features:** https://developers.openai.com/codex/cli/features
- **Discussion:** https://github.com/openai/codex/discussions/2150

### Plugin System
- Plugin marketplace with curated discovery
- `@plugin` mentions in chat for auto-including MCP/app/skill context
- MCP server management (list, add, remove, authenticate)
- Install-time auth checks, plugin/uninstall endpoint

### Comparison with Claude Code

| Feature | Claude Code | Codex CLI |
|---------|------------|-----------|
| Hook events | 12 lifecycle events | 2 (SessionStart, Stop) — experimental |
| Hook handler types | Command, Prompt, Agent | Command only |
| Can block actions | Yes (PreToolUse deny) | Not documented |
| Plugin system | Bundles hooks, skills, MCP, slash commands, subagents | Plugins with MCP, apps, skills |
| MCP support | Full (stdio + HTTP) | Full |
| Open source | No (CLI binary) | Yes |
| Customization depth | CLAUDE.md + hooks + skills + plugins | AGENTS.md + plugins + skills |

**Bottom line:** Claude Code has significantly deeper hook/lifecycle integration. Codex CLI is more minimalistic but open-source and catching up.

### Cross-Tool Ralph Loop
**Open Ralph Wiggum** (https://github.com/Th0rgal/open-ralph-wiggum) works with both Claude Code and Codex CLI (and Copilot, OpenCode) using the external bash-loop approach (no hooks needed). This is the most portable way to run Ralph across tools.

---

## 4. LLM Agentic Loop / Completion Patterns

### Key Resources
- **Simon Willison — "Designing Agentic Loops"** (Sep 2025): https://simonwillison.net/2025/Sep/30/designing-agentic-loops/
- **Simon Willison — Agentic Engineering Patterns**: https://simonw.substack.com/p/agentic-engineering-patterns
- **Addy Osmani — "My LLM Coding Workflow Going Into 2026"**: https://addyosmani.com/blog/ai-coding-workflow/
- **Ann Jose — "Agentic Coding In Practice"**: https://annjose.com/post/agent-coding-in-practice/

### Core Principles

1. **An agent = tools + loop + goal** (Willison's definition: "An LLM agent runs tools in a loop to achieve a goal")

2. **Small iterative loops** — Break work into small chunks. Reduce catastrophic error risk. Course-correct quickly. A structured "prompt plan" file contains a sequence of prompts for each task.

3. **Context management is critical** — In agentic mode, context fills fast. Bigger context = higher cost, slower responses, worse output. Keep context small, instructions clear, tools simple. Ralph Loop solves this by starting each iteration with fresh context.

4. **File-based state persistence** — Use files on disk (IMPLEMENTATION_PLAN.md, TODO lists, test results) as shared state between iterations. The agent reads current state from disk each time.

5. **Testing as validation** — The value of coding agents is "massively amplified by a good, cleanly passing test suite." Tests serve as the automated completion detector.

6. **Supervised vs autonomous** — Spectrum from fully supervised (approve every command) to fully autonomous (Ralph loop). The sweet spot depends on task risk and complexity.

7. **Brute force is valid** — "If you can reduce your problem to a clear goal and a set of tools that can iterate towards that goal, a coding agent can often brute force its way to an effective solution." (Willison)

### Completion Detection Approaches

| Approach | How It Works | Used By |
|----------|-------------|---------|
| **Test-driven** | Loop until all tests pass | Ralph (most common) |
| **Plan-driven** | Agent checks off items in IMPLEMENTATION_PLAN.md, loop ends when all done | ghuntley's Ralph |
| **LLM self-assessment** | Agent decides it's done, Stop hook asks "are you really done?" | Claude Code Stop hook |
| **Max iterations** | Hard cap on loop count | All Ralph variants (safety) |
| **Git diff analysis** | If no meaningful changes in last N iterations, stop | Some custom implementations |
| **External validation** | CI pipeline, linter, type checker passes | Production workflows |

---

## 5. Plugin vs MCP Server for Iterative Tasks

### The Claude Code Customization Stack

| Layer | What It Is | Best For |
|-------|-----------|----------|
| **CLAUDE.md** | Project instructions | Static rules, coding standards |
| **Skills** | Markdown files teaching Claude *how* to do things | Methodology, procedures |
| **Hooks** | Deterministic lifecycle interceptors | Quality gates, automation, loop control |
| **MCP Servers** | External tool/data access | GitHub, databases, APIs, browsers |
| **Plugins** | Bundles of skills + hooks + MCP + slash commands + subagents | Complete workflow packages |

- **Guide:** https://www.morphllm.com/claude-code-skills-mcp-plugins
- **Deep dive:** https://www.ado.im/posts/claude-customization-stack-mcp-skills-plugins/
- **Architecture:** https://alexop.dev/posts/understanding-claude-code-full-stack/

### For a Ralph-Style Iterative Loop, Which to Use?

**Plugin (recommended for loop control):**
- Can include Stop hooks that block exit and re-feed prompts — this IS the loop mechanism
- Can bundle the complete workflow: hooks + skills + slash commands + subagents
- Distributable as a single installable unit for teams
- Has access to all 12 lifecycle events
- The official Ralph Wiggum implementation IS a plugin

**MCP Server (not suitable for loop control):**
- MCP servers provide tools — they cannot intercept agent lifecycle
- Cannot block Claude from stopping (no Stop hook equivalent)
- Context overhead: each MCP server adds to context window
- Good for providing external data/actions that the loop *uses* (e.g., fetching test results from CI)
- "MCP is great for tools. Terrible for agents." (https://blog.vtemian.com/post/mcp-is-great-for-tools-terrible-for-agents/)

**External Bash Loop (most portable):**
- No plugin or MCP needed — just a bash script wrapping `claude` CLI
- Works with any agent (Claude Code, Codex, Copilot, OpenCode)
- State persists via files on disk
- Each iteration gets completely fresh context (best for long tasks)
- Trade-off: loses in-session context (must re-read everything from disk)

### Decision Matrix

| Requirement | Use Plugin | Use MCP | Use Bash Loop |
|-------------|-----------|---------|---------------|
| Control agent lifecycle (stop/restart) | Yes | No | Yes (external) |
| Access external systems (DB, API) | Via bundled MCP | Yes | No |
| Cross-tool compatibility (Codex, etc.) | No (Claude only) | Partially | Yes |
| Fresh context each iteration | No (same session) | N/A | Yes |
| Team distribution | Yes (installable) | Yes (config) | Yes (script) |
| Long-running tasks (hours) | Risky (context grows) | N/A | Best (fresh each time) |
| Intercept specific tool calls | Yes (PreToolUse) | No | No |

### Recommendation
For a Ralph-style loop in Claude Code:
- **Short tasks (<30 min):** Use the official **Ralph Wiggum plugin** (Stop hook keeps session alive)
- **Long tasks (hours):** Use an **external bash loop** (fresh context each iteration, file-based state)
- **Cross-tool:** Use **Open Ralph Wiggum** CLI wrapper
- **Combine with MCP:** If you need external system access during the loop, add MCP servers alongside the plugin/bash loop

---

## Key Takeaways

1. **Ralph is fundamentally simple** — a while-true loop with file-based state. The power is in the pattern, not the implementation complexity.

2. **Hooks are the mechanism** — Claude Code's Stop hook is what makes the in-session Ralph loop possible. The 12 lifecycle events give deep control.

3. **Codex CLI is catching up** — its experimental hooks engine (SessionStart + Stop) mirrors Claude Code's approach, but with far fewer events and no blocking capability documented yet.

4. **Plugin > MCP for loop control** — MCP servers cannot intercept lifecycle events. Plugins can bundle hooks that control the loop.

5. **External bash loops are most portable** — work with any agent, provide fresh context, and avoid context window growth. The trade-off is needing to re-read state from disk.

6. **Completion detection is the hard problem** — tests, plan checklists, LLM self-assessment, and max-iterations are all valid approaches, often combined.
