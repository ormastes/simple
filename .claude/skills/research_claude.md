# Research (Claude) Skill — Step 1 of 5

**Pipeline:** research_claude -> `/research_codex` -> `/design_gemini` -> `/design_codex` -> `/design_claude`

Claude performs local + domain research using parallel agent teams, producing research documents and draft requirement options.

## Inputs

- Feature name or description from user
- Existing docs in `doc/` vault

## Outputs

- `doc/01_research/local/<feature>.md` — local implementation research
- `doc/01_research/domain/<feature>.md` — domain/external research
- Draft requirement options in `doc/02_requirements/feature/` and `doc/02_requirements/nfr/`

## Phase 1: Local Implementation Research

### Tools

| Tool | Usage |
|------|-------|
| Simple MCP | `bin/simple query workspace-symbols --query <term>`, `bin/simple query references <file> <line>`, `bin/simple query hover <file> <line>` |
| LSP Plugin | `bin/simple query definition <file> <line>`, `bin/simple query completions <file> <line>` |
| Obsidian CLI | Search `doc/` vault for existing documentation |

### Agent Team (parallel)

Spawn two parallel agents:

- **Agent 1 (Code Search):** Searches `src/` via Simple MCP + LSP plugin
  - Find related types, functions, modules
  - Trace call chains and dependencies
  - Identify integration points and affected pipeline stages
  - Collect code examples and existing patterns

- **Agent 2 (Doc Search):** Searches `doc/` via Obsidian CLI
  - Find prior research, design docs, ADRs
  - Check feature specs and requirement docs
  - Locate related guides and rules
  - Collect references to existing decisions

### Merge

Combine Agent 1 + Agent 2 results into `doc/01_research/local/<feature>.md`.

## Phase 2: Domain Research

### Tools

| Tool | Usage |
|------|-------|
| Playwright CLI | Web search for external knowledge, papers, API docs, prior art |
| Obsidian CLI | Cross-reference existing research in `doc/01_research/domain/` |

### Process

1. Search existing `doc/01_research/domain/` for prior work on this topic
2. Web search for external knowledge: papers, language design references, API docs, comparable implementations
3. Synthesize findings into `doc/01_research/domain/<feature>.md`

## Phase 3: Requirement Samples

Generate draft requirement option sets for user review in Step 2:

- **Feature requirements** -> `doc/02_requirements/feature/<feature>_options.md`
  - Multiple implementation approaches with trade-offs
  - Scope variants (minimal, standard, full)
- **NFR requirements** -> `doc/02_requirements/nfr/<feature>_options.md`
  - Performance targets, reliability, maintainability
  - Compatibility and migration considerations

These are DRAFT options — the user selects from them in `/research_codex` (Step 2).

## Research Document Format

```markdown
# <Feature> - Research & Implementation Plan
**Date:** YYYY-MM-DD  |  **Status:** Research Phase

## 1. Problem Analysis (current state + requirements)
## 2. Proposed Solution (architecture + code examples)
## 3. Integration with Existing Infrastructure
## 4. Implementation Roadmap (phased tasks)
## 5. Testing Strategy
## 6. References
```

## Critical Rules

- NEVER skip local research — always check `src/` and `doc/` first
- Parallel agents must complete before merging
- Domain research must cross-reference local findings
- Draft requirements are OPTIONS, not final selections
- All output files use Markdown format
- Include code snippets from `src/` when they illustrate integration points

## Handoff

Pass all research results to `/research_codex` (Step 2):
- `doc/01_research/local/<feature>.md`
- `doc/01_research/domain/<feature>.md`
- `doc/02_requirements/feature/<feature>_options.md`
- `doc/02_requirements/nfr/<feature>_options.md`
