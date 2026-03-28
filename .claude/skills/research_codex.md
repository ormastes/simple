# Research Skill (Codex) -- Step 2: Forked Agent Research + Requirement Selection

**Pipeline:** Step 2 of 5 (after research_claude, before design_gemini)

## Prerequisites
- `doc/01_research/local/<feature>.md` from Step 1
- `doc/01_research/domain/<feature>.md` from Step 1

## Local Research (Codex)

### Tools
- **Simple MCP:** Same query tools as Step 1
- **LSP MCP:** Code intelligence via LSP
- **Obsidian CLI:** Doc vault search

### Agent Model
Uses **forked agents** (independent, parallel, no shared state) to validate and extend Claude's research findings.

## Domain Research (Codex)

- **Playwright CLI** for web research
- **Obsidian CLI** for doc vault search
- Cross-reference with Claude's domain research

## Requirement Generation

Generate requirement sample OPTIONS with pros/cons/effort:
- Feature requirements: `doc/02_requirements/feature/<feature>_options.md`
- NFR requirements: `doc/02_requirements/nfr/<feature>_options.md`
- Architecture/design selection options

## User Decision Phase

Present all options to user:
- "What features and NFR to implement and how?"
- User selects from requirement options
- User selects architecture/design approach
- **NEVER auto-select** -- always get explicit user choice

## Cleanup Phase

After user selects:
1. Remove unchosen requirement option files
2. Write final approved requirements:
   - `doc/02_requirements/feature/<feature>.md`
   - `doc/02_requirements/nfr/<feature>.md`

## Handoff
Pass chosen requirements to `/design_gemini` (Step 3).
