# Simple Language Compiler - Development Guide

**Also available as:** [AGENTS.md](AGENTS.md) (redirect to this file)

Impl in simple unless it has big performance differences.

**100% Pure Simple** - No Rust source. Self-hosted compiler written entirely in Simple.

See `/architecture` skill for binary architecture, project structure, and compiler pipeline.

---

## Agents (Task Tool)

Located in `.claude/agents/`. Usage: `Read .claude/agents/<name>.md and use its rules to <task>`

| Agent | Use When |
|-------|----------|
| **code** | Writing/editing Simple code |
| **test** | Writing tests, fixing failures |
| **debug** / **debug-analyst** | Investigating bugs, DAP+LSP |
| **explore** | Finding files, researching |
| **docs** | Writing docs, reports |
| **vcs** | Committing, pushing (jj/git) |
| **infra** | MCP, database, stdlib, SFFI |
| **build** | Building, releases |
| **ml** | ML features, neural networks |
| **shell-runner** / **build-runner** / **test-runner** / **lint-runner** | Offload command output |

---

## Skills

Invoke with `/skill-name`. Located in `.claude/skills/`. Key skills:

`vcs` `test` `coding` `design` `architecture` `research` `debug` `debug-lsp` `stdlib` `todo` `doc` `deeplearning` `sffi` `database` `mcp` `release` `cuda` `t32` `rule` `worktree` `impl` `refactor` `agents`

**Full Syntax Reference:** `doc/guide/quick_reference/syntax_quick_reference.md`
**Test Template:** `.claude/templates/sspec_template.spl`

---

## Critical Rules

### Version Control
- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `jj bookmark set main -r @- && jj git push --bookmark main`
- Fetch: `jj git fetch && jj rebase -d main@origin`

### Language
- **ALL code in `.spl` or `.shs`** - No Python, no Bash (except 3 bootstrap scripts in `scripts/`)
- **Generics:** `<>` not `[]` - `Option<T>`, `List<Int>`
- **Pattern binding:** `if val` not `if let`
- **Constructors:** `Point(x: 3, y: 4)` not `.new()`
- **`?` is operator only** - never in names. Use `.?` over `is_*` predicates
- **NO inheritance** - use composition, alias forwarding, traits, or mixins
- **SDN format** for all config/data files, not JSON/YAML
- **NEVER directly edit `.sdn` database files** — use the database API

### Tests
- **NEVER skip/ignore** failing tests without user approval
- **Built-in matchers only:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution

### TODOs
- **NEVER convert TODO/FIXME to NOTE** - that hides work, not resolves it
- Either **implement** the TODO or **delete the code entirely**

### Code Style
- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **DO NOT ADD REPORT TO GIT** unless requested

---

## Setup

```bash
sh config/mcp/install.shs
```

---

## Quick Commands

```bash
bin/simple build                    # Debug build
bin/simple build --release          # Release build
bin/simple test                     # All tests
bin/simple test path/to/spec.spl   # Single file
bin/simple build lint               # Linter
bin/simple build fmt                # Formatter
bin/simple build check              # All checks
bin/simple fix file.spl --dry-run   # Preview fixes
bin/simple todo-scan                # Update TODO tracking
bin/simple duplicate-check src/     # Duplication detection
```

See `/commands` skill for full command reference.

---

## Runtime Limitations (CRITICAL)

See `/coding` skill for full list. Key issues:
- **Error handling:** Use `Result<T, E>` + `?` operator (no try/catch/throw — by design)
- **Multi-line booleans** - wrap in parentheses: `if (a and\n   b):` works
- **Nested closure capture** - can READ outer vars, CANNOT MODIFY
- **Chained methods broken** - use intermediate `var`
- **NO inheritance** - by design
- **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `match`, `skip`, `pass_todo`, `pass_do_nothing`, `pass_dn`
