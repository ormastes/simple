# Shell Runner Agent — Research & Design

**Status:** Implemented
**Date:** 2026-03-14

## Problem

Direct Bash calls from the main Claude Code agent flood the context window with command output. Large build logs, test results, and diagnostic output consume tokens that should be reserved for reasoning and code editing.

## Solution

A dedicated **shell-runner** subagent that:
- Handles all terminal command execution in an isolated context
- Returns only concise summaries to the main agent
- Keeps the main agent's context window clean for code work

## Architecture

### Claude Code Agent Routing

```
Main Agent (opus)
  ├── shell-runner agent (sonnet) ← terminal commands
  ├── code agent ← code editing
  ├── test agent ← test writing
  ├── explore agent ← codebase research
  └── ... other agents
```

### How Routing Works

Claude Code uses **three mechanisms** for controlling Bash access:

| Mechanism | Type | Purpose |
|-----------|------|---------|
| **Subagent description** | Soft routing | Claude reads the description and decides to delegate |
| **Permission settings** | Policy | `.claude/settings.json` allow/deny rules |
| **PreToolUse hooks** | Hard enforcement | Shell script that validates/blocks commands |

### Key Distinction

- **Subagent** — isolated worker with its own prompt, model, and tool restrictions
- **Bash tool** — terminal command execution capability (available in main agent AND subagents)
- **Plugin** — packaging/distribution mechanism that can bundle MCP servers, hooks, and subagents
- **Settings** — global/project/local JSON files controlling permissions, hooks, etc.

## Implementation

### 1. Agent File: `.claude/agents/shell-runner.md`

Created with:
- Tools: `Bash, Read, Grep, Glob`
- Model: `sonnet` (fast, cheap for shell work)
- Description optimized for auto-routing by Claude

### 2. Permission Settings: `.claude/settings.json`

Existing settings already define Bash allow/deny rules. No changes needed — the shell-runner agent inherits these permissions.

### 3. Hook-Based Enforcement (Optional, Not Implemented)

For hard enforcement (force ALL bash through the agent), a PreToolUse hook could intercept direct Bash calls:

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": ".claude/hooks/validate-bash.sh"
          }
        ]
      }
    ]
  }
}
```

**Not implemented** because:
- Soft routing via description is sufficient for most cases
- Hard enforcement would block the main agent from simple `git status` / `ls` calls
- The context-mode plugin already handles output size management

### 4. Plugin Approach (Not Needed)

Plugins can bundle MCP servers and subagents, but this is overkill for a single project. Plugins are for cross-project distribution.

## Limitation

There is **no way to force** "all Bash calls must go through shell-runner." Routing is driven by:
1. Claude's internal delegation logic
2. Subagent descriptions (soft guidance)
3. Permissions and hooks (hard policy)

The main agent may still use Bash directly for trivial commands (`ls`, `git status`). This is acceptable — the goal is to offload **heavy** shell work, not eliminate all direct Bash usage.

## Usage

From the main agent:
```
Use the shell-runner agent to run the test suite and report results.
Use the shell-runner agent to build the project in release mode.
Use the shell-runner agent to check jj status and recent log.
```

Or Claude auto-routes based on the agent description when it detects a shell-heavy task.
