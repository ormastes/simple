# Build, Test & Lint Runner Agents — Research & Design

**Status:** Implemented
**Date:** 2026-03-14

## Problem

Direct `bin/simple build`, `bin/simple test`, and `bin/simple build lint` calls from the main agent flood the context window with large output (build logs, test results, lint warnings). This wastes tokens that should be reserved for reasoning and code editing.

## Solution

Three dedicated subagents that handle execution in isolated contexts and return only concise summaries:

| Agent | Commands | Purpose |
|-------|----------|---------|
| **build-runner** | `bin/simple build [--release]` | Build execution |
| **test-runner** | `bin/simple test [path]` | Test execution |
| **lint-runner** | `bin/simple build lint/fmt/check` | Quality checks |

## Architecture

```
Main Agent (opus) — reasoning + code editing
  ├── build-runner (sonnet) ← build commands
  ├── test-runner (sonnet) ← test commands
  ├── lint-runner (sonnet) ← lint/fmt/check commands
  ├── shell-runner (sonnet) ← general shell tasks
  ├── code agent ← code editing
  └── ... other agents
```

## Routing Mechanisms

Three layers of control, from soft to hard:

### Layer 1: Subagent Descriptions (Soft Routing)

Claude reads agent descriptions and delegates matching tasks. Each agent's description is tuned for specific command patterns:
- "Use this agent INSTEAD of direct `bin/simple build` calls"
- "Use this agent INSTEAD of direct `bin/simple test` calls"

### Layer 2: Permission Settings (Policy)

`.claude/settings.json` can deny direct command patterns:

```json
{
  "permissions": {
    "deny": [
      "Bash(bin/simple build *)",
      "Bash(bin/simple test *)",
      "Bash(bin/simple build lint*)"
    ]
  }
}
```

**Not implemented** — soft routing is sufficient and deny rules would also block the subagents themselves (they inherit permissions).

### Layer 3: PreToolUse Hooks (Hard Enforcement)

A hook script can intercept Bash calls and block specific patterns:

```json
{
  "hooks": {
    "PreToolUse": [{
      "matcher": "Bash",
      "hooks": [{
        "type": "command",
        "command": ".claude/hooks/guard-simple.sh"
      }]
    }]
  }
}
```

**Not implemented** — would need to distinguish main agent vs subagent calls, adding complexity without clear benefit.

## Why Not Wrapper Scripts?

The research suggested wrapper scripts (`.claude/scripts/run-build.sh`, etc.) that agents call instead of raw commands. This project doesn't need them because:

1. Build/test commands are already simple and well-defined (`bin/simple build`, `bin/simple test`)
2. No complex pre-build steps needed (no `simple project doctor`, no `simple deps sync`)
3. Wrapper scripts add indirection without value for this project

## Design Decisions

### Model: sonnet for all runners
- Build/test/lint output parsing doesn't need opus-level reasoning
- Sonnet is faster and cheaper for command execution + summarization

### No YAML frontmatter
- Existing project agents use plain markdown format
- Consistency with `code.md`, `build.md`, `test.md`, etc.

### Separate agents vs. one unified runner
- Separate agents give Claude better routing signals (description matching)
- Each agent can have domain-specific summary logic
- The existing `shell-runner` handles general shell tasks not covered by specific runners

## Limitation

Same as shell-runner: no hard enforcement mechanism to force ALL build/test calls through agents. The main agent may still use direct Bash for trivial checks. The goal is to offload **heavy output** tasks, not eliminate all direct usage.

## Usage

```
Use the build-runner agent to build in release mode.
Use the test-runner agent to run all tests.
Use the test-runner agent to run test/unit/compiler/loader/use_lazy_spec.spl
Use the lint-runner agent to check code quality.
```
