---
name: spipe_doc_wiki_refactor
description: "SPipe documentation/wiki refactoring pass. Use during SPipe refactor and ship phases to update docs, wiki-style process knowledge, feature/layer expert links, and stale references after implementation changes."
---

# SPipe Doc/Wiki Refactor

Run this as a support skill during SPipe Phase 6 (Refactor) and Phase 8
(Ship). Its job is documentation hygiene, not product behavior.

## Inputs

- `.spipe/<feature>/state.md`
- Files changed by the SPipe implementation and specs
- Existing docs under `doc/`
- Process/knowledge files under `.claude/skills/`, `.claude/agents/`,
  `.codex/skills/`, and `doc/00_llm_process/`

## Actions

1. Identify docs and wiki-style knowledge that mention the changed feature,
   changed APIs, changed commands, or changed file paths.
2. Update stale links, command names, phase references, and file paths.
3. Add or refresh concise cross-links in affected feature/layer expert docs.
4. Refactor duplicated documentation into a single canonical reference when
   multiple docs repeat the same process rule.
5. Keep completion reports in `doc/09_report/`; do not turn process updates
   into reports.
6. Record changed doc/wiki files in `.spipe/<feature>/state.md`.

## Guardrails

- Do not change implementation behavior.
- Do not create broad documentation rewrites unrelated to the feature.
- Do not overwrite another agent's research; append with a dated note if needed.
- Keep process knowledge reusable and concise.
- Prefer fixing broken links over adding new parallel explanations.

## Exit Criteria

- No stale references remain in touched SPipe/process docs.
- Changed commands and paths are reflected in relevant guides or skills.
- `.spipe/<feature>/state.md` lists doc/wiki updates or states that none were
  needed.
