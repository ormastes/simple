# Research Skill (Claude) -- Step 1: Local + Domain Research

**Pipeline:** Step 1 of 5 (research_claude -> research_codex -> design_gemini -> design_codex -> design_claude)

## Local Implementation Research

### Tools
- **Simple MCP:** `bin/simple query workspace-symbols`, `bin/simple query references`, `bin/simple query hover`
- **LSP Plugin:** `bin/simple query definition`, `bin/simple query completions`, `bin/simple query call-hierarchy`
- **Obsidian CLI:** Search `doc/` vault for existing research/design/requirement docs

### Agent Team
Spawn parallel agents:
- **Agent 1:** Source code exploration via MCP + LSP (search `src/`)
- **Agent 2:** Doc exploration via Obsidian CLI (search `doc/`)
- Merge results into research summary

### Output
- `doc/01_research/local/<feature>.md`

## Domain Research

### Tools
- **Playwright CLI:** Web search for external references, API docs, papers
- **Obsidian CLI:** Search existing `doc/01_research/domain/` for prior work

### Workflow
1. Search existing research docs for prior analysis
2. Web search via Playwright for external knowledge
3. Synthesize into research document

### Output
- `doc/01_research/domain/<feature>.md`

## Requirement Samples

Generate draft requirement options:
- Feature requirements -> `doc/02_requirements/feature/<feature>_draft.md`
- NFR requirements -> `doc/02_requirements/nfr/<feature>_draft.md`

## Research Document Format

```markdown
# Title - Research & Implementation Plan
**Date:** YYYY-MM-DD  |  **Status:** Research Phase
## 1. Problem Analysis (current state + requirements)
## 2. Proposed Solution (architecture + code examples)
## 3. Integration with Existing Infrastructure
## 4. Implementation Roadmap (phased tasks)
## 5. Testing Strategy
## 6. References
```

## Handoff
Pass research results to `/research_codex` (Step 2).
