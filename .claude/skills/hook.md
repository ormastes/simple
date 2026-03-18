---
name: hook
description: Claude Code hook system documentation, all 8 hooks, enable/disable, and how to add new hooks
---

# Claude Code Hook System

## Overview

Hooks are shell scripts that run automatically at specific points in Claude Code's lifecycle. They enforce project rules, provide quality gates, and automate repetitive tasks.

## Hook Events

| Event | When | Use For |
|-------|------|---------|
| `PreToolUse` | Before a tool executes | Block dangerous operations, validate inputs |
| `PostToolUse` | After a tool executes | Warn about code quality issues, remind about lint |
| `Stop` | When Claude stops responding | Session summaries, auto-checkpoints, quality checks |

## Hook Protocol

- **Input**: JSON on stdin containing `tool_name`, `tool_input`, and context
- **Output**: Messages to stdout (shown to user)
- **Exit codes**: `0` = pass/warn, `2` = block (PreToolUse only)

## Active Hooks

### PreToolUse Hooks
| Script | Matcher | Behavior | Exit |
|--------|---------|----------|------|
| `binary-guard.sh` | Bash | Block rm/mv/truncate/cp on protected binaries and .sdn files | 2 (block) |

### PostToolUse Hooks  
| Script | Matcher | Behavior | Exit |
|--------|---------|----------|------|
| `comment-replace-detect.sh` | Edit\|Write | Warn if code replaced with comments | 0 (warn) |
| `auto-lint-warn.sh` | Edit\|Write | Remind to lint .spl/.shs files | 0 (remind) |

### Stop Hooks
| Script | Behavior | Exit |
|--------|----------|------|
| `agent-loop-hook.shs` | Agent loop bookkeeping (existing) | 0 |
| `todo-check.sh` | Warn about new TODO/FIXME lines | 0 (warn) |
| `completion-guard.sh` | List uncommitted changes and new TODOs | 0 (warn) |
| `auto-checkpoint.sh` | Auto-describe uncommitted changes as WIP | 0 |
| `pure-simple-guard.sh` | Warn if .rs files modified | 0 (warn) |
| `session-summary.sh` | Show jj diff --stat summary | 0 |

## Adding a New Hook

1. Create script in `scripts/hooks/claude/`:
   ```bash
   #!/usr/bin/env bash
   set -euo pipefail
   INPUT=$(cat)
   # Parse JSON input, do checks
   # echo messages to stdout
   # exit 0 (pass/warn) or 2 (block, PreToolUse only)
   ```
2. Make executable: `chmod +x scripts/hooks/claude/your-hook.sh`
3. Add entry to `.claude/settings.json` under the appropriate event
4. Test: `echo '{"tool_name":"Bash","tool_input":{"command":"test"}}' | bash scripts/hooks/claude/your-hook.sh`

## Enabling/Disabling Hooks

- **Disable**: Remove or comment out the hook entry in `.claude/settings.json`
- **Temporarily skip**: Rename script (e.g., `mv hook.sh hook.sh.disabled`)
- **Re-enable**: Restore the settings.json entry or rename back

## Hook Location

All hook scripts: `scripts/hooks/claude/`
Settings: `.claude/settings.json` -> `hooks` section
