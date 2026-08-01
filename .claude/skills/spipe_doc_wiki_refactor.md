---
name: spipe_doc_wiki_refactor
description: "SPipe documentation/wiki refactoring pass. Use during SPipe refactor before final verification to update docs, wiki-style process knowledge, feature/layer expert links, and stale references after implementation changes."
---

# SPipe Doc/Wiki Refactor

Run this as a support skill during SPipe Phase 6 (Refactor), before final
verification. Ship consumes verify evidence and must not repair stale
doc/wiki/process links. Its job is documentation hygiene, not product behavior.

## Inputs

- `.spipe/<feature>/state.md`
- Files changed by the SPipe implementation and specs
- Existing docs under `doc/`
- Process/knowledge files under `.codex/skills/`, `.agents/skills/`,
  `.claude/skills/`, `.claude/agents/spipe/`, `.gemini/commands/`,
  `doc/07_guide/`, `doc/06_spec/`, and `doc/00_llm_process/`
- The private overlay doc/wiki tree (read order `00 -> 10 -> 20`):
  - `.spipe/00_llm_process/` — LLM pipeline/process definitions; reference the wiki
  - `.spipe/10_llm_wiki/` — curated LLM wiki, distilled from raw docs
  - `.spipe/20_raw_doc/` — raw source documents the wiki is built from
  - `.spipe/core/` — vendored read-only copy of the public project (stripped
    clone, pull-only; never edit or push from here)

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
7. When a change adds or replaces evidence wrappers, update the canonical guide
   or plan reference that names the wrapper command, report path, required
   lanes, and host-unavailable behavior.
8. For SPipe/spec-adjacent work, run
   `find doc/06_spec -name '*_spec.spl' | wc -l` and keep the result at `0`;
   executable specs belong under `test/`, not `doc/06_spec`.
9. For workflow, tool-contract, evidence-wrapper, generated-manual, or
   verification-contract changes, refresh the matching `doc/07_guide`,
   `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
   `.claude/agents/spipe/`, and `.gemini/commands/` instructions before final
   verification. Stale process docs are verify failures, not release cleanup.
10. Maintain the overlay doc/wiki tree when a change touches it: distill new
   `.spipe/20_raw_doc/` material into `.spipe/10_llm_wiki/`, and keep
   `.spipe/00_llm_process/` references to the wiki current. Edit raw docs and
   wiki, never `.spipe/core/` (vendored read-only snapshot; refresh it by
   re-running `add_spipe_core`, not by hand-editing).

## Guardrails

- Do not change implementation behavior.
- Keep `.spipe/10_llm_wiki/` public-safe: no secrets, tokens, or private URLs.
- Do not create broad documentation rewrites unrelated to the feature.
- Do not overwrite another agent's research; append with a dated note if needed.
- Keep process knowledge reusable and concise.
- Prefer fixing broken links over adding new parallel explanations.

## Exit Criteria

- No stale references remain in touched SPipe/process docs.
- Changed commands and paths are reflected in relevant guides or skills.
- Workflow/tooling/evidence/spec/verification contract changes refreshed the
  matching process docs listed above, or the lane state records an explicit
  `N/A` with reason.
- `.spipe/<feature>/state.md` lists doc/wiki updates or states that none were
  needed.
