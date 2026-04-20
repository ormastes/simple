# Codex Agent — Self-Sufficient Feature Pipeline

**Full pipeline (ideal):** `$research` -> `$design` -> `$impl` -> `$verify` -> `$release`

Each step is **self-sufficient** — if prior steps were not done (by Claude, Gemini, or anyone), do them yourself before proceeding.

## Cooperative Phase Dev

In multi-LLM cooperative mode, Codex owns **Step 2 (research)** and **Step 4 (architecture+design)**:
```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI)
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
See: `doc/guide/llm_cooperative_dev_phase.md`

## Skills Reference

| Skill | File | Purpose |
|-------|------|---------|
| `$research` | `.codex/skills/research/SKILL.md` | Research + requirement options |
| `$design` | `.codex/skills/design/SKILL.md` | Architecture + system tests |
| `$impl` | `.codex/skills/impl/SKILL.md` | 15-phase implementation |
| `$verify` | `.codex/skills/verify/SKILL.md` | Production readiness check |
| `$release` | `.codex/skills/release/SKILL.md` | Version bump + tag |
| `$architecture` | `.codex/skills/architecture/SKILL.md` | MDSOC, ADR writing |
| `$mdsoc` | `.codex/skills/mdsoc-architecture-writing/SKILL.md` | MDSOC architecture docs |
| `$system_test` | `.codex/skills/system_test/SKILL.md` | SSpec test design |
| `$coding` | `.codex/skills/coding/SKILL.md` | Simple language rules |

---

## Self-Sufficiency Rule

Before starting any step, **check if prerequisite artifacts exist**:

| If you need... | Check for... | If missing... |
|----------------|-------------|---------------|
| Research | `doc/01_research/local/<feature>.md` | Do local + domain research yourself |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Research first, then generate + ask user to select |
| UI design | `doc/05_design/<feature>_tui.md` | Create TUI/GUI mockups yourself |
| Architecture | `doc/04_architecture/<feature>.md` | Design architecture yourself |
| System tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` | Create SSpec tests yourself |
| Detail design | `doc/05_design/<feature>.md` | Create detail design yourself |
| Implementation | `src/**/<feature>.spl` | Implement the feature |

**Never fail because a prior step wasn't done by another LLM. Just do it.**

---

## Available Tools

| Tool | Purpose |
|------|---------|
| **Simple MCP** | `bin/simple query workspace-symbols`, `references`, `hover` — codebase search |
| **Simple LSP MCP** | `bin/simple query definition`, `completions` — code navigation |
| **Context7 MCP** | External library documentation lookup |
| **Playwright CLI** | `npx playwright` — web scraping, browser automation, domain research |

---

## Step 1: Research

Check: `doc/01_research/local/<feature>.md` and `doc/01_research/domain/<feature>.md` exist?

If missing, do both:

### Local Research
- Search `src/` for related types, functions, modules, call chains (use Simple MCP + LSP MCP)
- Search `doc/` for prior research, design docs, ADRs
- Output: `doc/01_research/local/<feature>.md`

### Domain Research
- Web search via Playwright CLI for external knowledge, papers, prior art
- Output: `doc/01_research/domain/<feature>.md`

### Requirement Options
- Generate feature options with pros/cons/effort: `doc/02_requirements/feature/<feature>_options.md`
- Generate NFR options: `doc/02_requirements/nfr/<feature>_options.md`
- **Ask user** to select, then write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

---

## Step 2: Design

Check: `doc/04_architecture/<feature>.md` and `doc/05_design/<feature>.md` exist?

If missing, do all:

### UI Design (if feature has UI)
- TUI mockups: `doc/05_design/<feature>_tui.md`
- GUI mockups: `doc/05_design/<feature>_gui.md`

### Architecture
- Evaluate patterns, apply MDSOC where appropriate
- Output: `doc/04_architecture/<feature>.md`

### System Test Design
- SSpec BDD tests: `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl`
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`

### Detail Design
- Data structures, algorithms, module interactions, error handling
- Output: `doc/05_design/<feature>.md`
- Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md`

---

## Step 3: Implementation

See `/impl` skill (15-phase workflow). Key phases:
1. Implement in `src/**/<feature>.spl`
2. Unit + integration tests (80%+ coverage)
3. Doctest for public fns
4. Bug reports, duplication check, refactoring
5. Full test suite pass

---

## Step 4: Verify

Run `/verify` — production readiness check:

| Check | Fail Condition |
|-------|---------------|
| SSpec Tests | `pass_todo`, `expect(true).to_equal(true)`, empty bodies |
| Implementation | Stub functions, hardcoded returns, TODO-only bodies |
| Requirements | REQ-NNN without implementation or test coverage |
| NFR | Targets without verification mechanism |
| Architecture | `doc/04_architecture/` missing or outdated |
| Design | `doc/05_design/` missing or outdated |

Additional required checks for compiler/core/lib or MCP/LSP changes:
- `sh scripts/check-core-runtime-smoke.shs <runtime>`
- `SIMPLE_BINARY=<runtime> sh scripts/check-mcp-native-smoke.shs`
- If npm/package/release path changed: `sh scripts/check-mcp-package-smoke.shs`

Must show `STATUS: PASS` before release.

---

## Step 5: Release

Run `/release` — version bump, CHANGELOG, commit, tag, push.

---

## MCP Registry Distribution

MCP server available via npm: `@simple-lang/mcp-server`
- Package: `tools/mcp-registry/` (npm wrapper for native binary)
- Registry: `registry.modelcontextprotocol.io`
- Guide: `doc/07_guide/tooling/ai_cli_registration.md`

---

## Critical Rules

- **Self-sufficient**: never fail because another LLM didn't do its step — do it yourself
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- NEVER overwrite another LLM's research — append and annotate
- All requirement options must include pros, cons, and effort estimate
- User MUST select requirements — never auto-select
- Unchosen options are DELETED, not archived
- For MCP, LSP, and tool-server work, design must review startup path, hot request paths, cache or index strategy, invalidation strategy, and startup/latency/RSS targets
- When `src/compiler/**` or `src/lib/**` changes can affect MCP/LSP startup or language surface, finish by running the core runtime smoke and MCP native smoke checks; if publish/package flow changed, also run the isolated npm package smoke check
- Production wrappers should execute cached compiled artifacts rather than raw source entrypoints
- Repeated full-tree scans, repeated rereads, shell-outs, and retry sleeps in hot request handlers require explicit design justification and verification evidence
- Verify perf-sensitive tooling with warm startup time, representative request latency, and max RSS on realistic fixtures

## Artifacts Summary

| Step | Artifact | Location |
|------|----------|----------|
| 1 | Local research | `doc/01_research/local/<feature>.md` |
| 1 | Domain research | `doc/01_research/domain/<feature>.md` |
| 1 | Feature requirements | `doc/02_requirements/feature/<feature>.md` |
| 1 | NFR requirements | `doc/02_requirements/nfr/<feature>.md` |
| 2 | Architecture | `doc/04_architecture/<feature>.md` |
| 2 | UI design | `doc/05_design/<feature>_tui.md`, `_gui.md` |
| 2 | Detail design | `doc/05_design/<feature>.md` |
| 2 | System tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` |
| 2 | Test plan | `doc/03_plan/sys_test/<feature>.md` |
| 2 | Agent tasks | `doc/03_plan/agent_tasks/<feature>.md` |
| 3 | Source code | `src/**/<feature>.spl` |
| 4 | Verify report | Terminal output (PASS/FAIL/WARN) |

# context-mode — MANDATORY routing rules

You have context-mode MCP tools available. These rules are NOT optional — they protect your context window from flooding. A single unrouted command can dump 56 KB into context and waste the entire session. Codex CLI does NOT have hooks, so these instructions are your ONLY enforcement mechanism. Follow them strictly.

## BLOCKED commands — do NOT use these

### curl / wget — FORBIDDEN
Do NOT use `curl` or `wget` in any shell command. They dump raw HTTP responses directly into your context window.
Instead use:
- `mcp__context-mode__ctx_fetch_and_index(url, source)` to fetch and index web pages
- `mcp__context-mode__ctx_execute(language: "javascript", code: "const r = await fetch(...)")` to run HTTP calls in sandbox

### Inline HTTP — FORBIDDEN
Do NOT run inline HTTP calls via `node -e "fetch(..."`, `python -c "requests.get(..."`, or similar patterns. They bypass the sandbox and flood context.
Instead use:
- `mcp__context-mode__ctx_execute(language, code)` to run HTTP calls in sandbox — only stdout enters context

### Direct web fetching — FORBIDDEN
Do NOT use any direct URL fetching tool. Raw HTML can exceed 100 KB.
Instead use:
- `mcp__context-mode__ctx_fetch_and_index(url, source)` then `mcp__context-mode__ctx_search(queries)` to query the indexed content

## REDIRECTED tools — use sandbox equivalents

### Shell (>20 lines output)
Shell is ONLY for: `git`, `mkdir`, `rm`, `mv`, `cd`, `ls`, `npm install`, `pip install`, and other short-output commands.
For everything else, use:
- `mcp__context-mode__ctx_batch_execute(commands, queries)` — run multiple commands + search in ONE call
- `mcp__context-mode__ctx_execute(language: "shell", code: "...")` — run in sandbox, only stdout enters context

### File reading (for analysis)
If you are reading a file to **edit** it → reading is correct (edit needs content in context).
If you are reading to **analyze, explore, or summarize** → use `mcp__context-mode__ctx_execute_file(path, language, code)` instead. Only your printed summary enters context. The raw file stays in the sandbox.

### grep / search (large results)
Search results can flood context. Use `mcp__context-mode__ctx_execute(language: "shell", code: "grep ...")` to run searches in sandbox. Only your printed summary enters context.

## Tool selection hierarchy

1. **GATHER**: `mcp__context-mode__ctx_batch_execute(commands, queries)` — Primary tool. Runs all commands, auto-indexes output, returns search results. ONE call replaces 30+ individual calls.
2. **FOLLOW-UP**: `mcp__context-mode__ctx_search(queries: ["q1", "q2", ...])` — Query indexed content. Pass ALL questions as array in ONE call.
3. **PROCESSING**: `mcp__context-mode__ctx_execute(language, code)` | `mcp__context-mode__ctx_execute_file(path, language, code)` — Sandbox execution. Only stdout enters context.
4. **WEB**: `mcp__context-mode__ctx_fetch_and_index(url, source)` then `mcp__context-mode__ctx_search(queries)` — Fetch, chunk, index, query. Raw HTML never enters context.
5. **INDEX**: `mcp__context-mode__ctx_index(content, source)` — Store content in FTS5 knowledge base for later search.

## Output constraints

- Keep responses under 500 words.
- Write artifacts (code, configs, PRDs) to FILES — never return them as inline text. Return only: file path + 1-line description.
- When indexing content, use descriptive source labels so others can `search(source: "label")` later.

## ctx commands

| Command | Action |
|---------|--------|
| `ctx stats` | Call the `stats` MCP tool and display the full output verbatim |
| `ctx doctor` | Call the `doctor` MCP tool, run the returned shell command, display as checklist |
| `ctx upgrade` | Call the `upgrade` MCP tool, run the returned shell command, display as checklist |
