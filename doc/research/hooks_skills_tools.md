# Hooks, Skills & Tools — Consolidated Research

## Hook Event Reference

Claude Code supports three lifecycle hook events:

| Event | Trigger | Stdin JSON | Can Block? |
|-------|---------|-----------|------------|
| `PreToolUse` | Before any tool call | `{tool_name, tool_input}` | Yes (exit 2) |
| `PostToolUse` | After any tool call | `{tool_name, tool_input, tool_output}` | No |
| `Stop` | When Claude stops responding | `{}` | No |

### Hook Configuration (settings.json)
```json
{
  "hooks": {
    "EventName": [
      {
        "matcher": "ToolNameRegex",
        "hooks": [
          { "type": "command", "command": "bash path/to/script.sh" }
        ]
      }
    ]
  }
}
```

## Tool Comparison Matrix

| Approach | Scope | Latency | Complexity | Best For |
|----------|-------|---------|-----------|----------|
| Hooks | Per-tool-call | Low (ms) | Shell script | Guards, reminders, auto-format |
| MCP Tools | On-demand | Medium | Server process | Data queries, external APIs |
| Skills | User-invoked | None | Markdown | Workflows, checklists, guides |
| Commands | User-invoked | None | Markdown redirect | Aliases to skills |
| Agents | Task-scoped | High | Markdown | Complex multi-step work |

## Decision Matrix: Hook vs MCP vs Command

| Need | Use |
|------|-----|
| Block dangerous operations | PreToolUse hook (exit 2) |
| Warn about code quality | PostToolUse hook (exit 0 + message) |
| Session cleanup/summary | Stop hook |
| Query external data | MCP tool |
| Guided workflow | Skill (user invokes with /name) |
| Quick alias | Command pointing to skill |

## Patterns from Reference Projects

### claudekit
- Individual hook scripts in dedicated directory
- Settings.json wiring with matchers
- Exit code protocol (0=pass, 2=block)

### Taskmaster
- MCP server for task management
- Skills for workflow orchestration

### GSD (Get Stuff Done)
- Hook-based enforcement of project rules
- Auto-checkpoint on session end

### Spec Kit
- Skill frontmatter for auto-routing
- description field enables Claude to match user intent to skills

## Skill Frontmatter Standard

```yaml
---
name: skill-name
description: One-line description for auto-routing
---
```

The `description` field is critical — Claude uses it to decide when to invoke skills automatically. Without it, skills only work via explicit `/skill-name` invocation.

## Key Findings

1. **Hook scripts should be individual files** — testable, version-controlled, easy to enable/disable
2. **Only binary-guard should block** — near-zero false positive rate required for blocking hooks
3. **Auto-lint should remind, not run** — running linter per-edit adds latency
4. **Stop hooks should warn, not block** — blocking session end is frustrating
5. **Skill frontmatter enables auto-routing** — critical for discoverability
