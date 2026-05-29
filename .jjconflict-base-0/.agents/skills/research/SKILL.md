---
name: research
description: Run local + domain research for a feature. Search src/ and doc/ for related code, web search for external knowledge, generate requirement options, ask user to select. Self-sufficient — does not depend on any prior step.
---

# Research — Self-Sufficient

**Self-sufficient.** Does not depend on any prior step or other LLM.

## Phase 1: Local Research

Search `src/` and `doc/` for related code, types, call chains, prior research, ADRs.

Output: `doc/01_research/local/<feature>.md`

## Phase 2: Domain Research

Web search for external knowledge, papers, language design references, prior art.

Output: `doc/01_research/domain/<feature>.md`

## Phase 3: Requirement Options

Generate options with pros/cons/effort for user selection:
- Feature: `doc/02_requirements/feature/<feature>_options.md`
- NFR: `doc/02_requirements/nfr/<feature>_options.md`

## Phase 4: User Decision

Ask: **"Which feature option and NFR targets?"**

After selection:
- Remove unchosen files
- Write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

## Multi-LLM Collaboration (optional)

If another LLM already did research, **extend it** — never overwrite.

## Rules

- NEVER skip local research — always check `src/` and `doc/` first
- Draft requirements are OPTIONS — user MUST select
- All code in `.spl` — no Python, no Bash
