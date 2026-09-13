# Research Skill (Codex) — Step 2: Forked Agent Research

See `lib/research_common.md` for shared format and templates.

## Cooperative Phase
**Step 2 of 5** in multi-LLM cooperative pipeline.
- Reads Claude Step 1 output from `doc/01_research/<domain>/<topic>/`
- Forks parallel research agents for deeper analysis
- Generates requirement option sets for user selection
- Plugin: `tools/claude-plugin/codex-research/`

## Input
- `doc/01_research/<domain>/<topic>/<feature>.md` (from Step 1)

## Forked Agent Pattern

Spawn 3 parallel Codex agents:
- **Agent A — Alternative Approaches:** Explore alternative architectures and patterns
- **Agent B — Requirement Validation:** Check requirements against Simple language constraints
- **Agent C — Risk Analysis:** Identify implementation risks and edge cases

Merge results into consolidated research.

## Output
- `doc/01_research/<domain>/<topic>/<feature>.md` — consolidated Codex research
- `doc/02_requirements/<domain>/<topic>/<feature>_options.md` — 2-3 requirement option sets for user selection

## Handoff
User selects requirement option, then proceed to `/ui` (Step 3) or `/arch` (Step 4).
