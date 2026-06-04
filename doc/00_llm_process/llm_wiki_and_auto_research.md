# llm wiki and auto-research

This repository already realizes the two patterns Andrej Karpathy describes as
**LLM Wiki** (a living, self-healing markdown knowledge base the agent writes and
maintains) and **Auto-Research** (a measure-edit-keep-or-revert improvement loop).
This page names those patterns and points at where Simple already implements them.
It does not introduce a new mechanism or duplicate the linked content — it is a map.

## llm wiki mapping

Karpathy's LLM Wiki has three layers (raw sources, the wiki, the interface) plus a
self-healing update step. The Simple equivalents are:

| Karpathy concept | Simple artifact |
|------------------|-----------------|
| Raw sources (notes, transcripts) | `doc/01_research/<domain>/` (language, compiler, lib, app, os, hardware, platform, runtime, ui, ml, infra), `doc/02_requirements/` |
| The wiki — concept pages + cross-links | Expert tree: `feature_expert/<feature>/skill.md`, `layer_expert/<layer>/skill.md`, plus submodule-linked `domain_expert/`, `tool_expert/`, `project_expert/` |
| Wiki structure (downstream knowledge) | `doc/04_architecture/`, `doc/05_design/`, `doc/06_spec/` (mirrored from `test/` paths) |
| The interface | Claude Code + the pipeline skills `/research` `/design` `/impl` `/verify` `/release` |
| Self-healing update | [`pipeline_next_step_plan.md`](pipeline_next_step_plan.md) §"Runtime Process" step 5, plus drift detection via `bin/simple llm-process-gen check` |
| "Don't delete raw sources" | `skeleton` records in [`llm_process_manifest.sdn`](llm_process_manifest.sdn) are durable and never overwritten by `generate`/`generate --force` (see [README](README.md)) |

## does spipe have a wiki-update step?

Yes. It is the knowledge-update obligation built into every pipeline stage.
After each stage the lead agent must:

- append or refresh links in the affected `feature_expert/<feature>/skill.md`
- append or refresh links in the affected `layer_expert/<layer>/skill.md`
- update the next-step plan status and handoff notes
- update `skill_command/` only when reusable, project-neutral process knowledge changed

There is also an explicit doc/wiki refactor checkpoint during SPipe Refactor and
Ship. The checkpoint uses `.claude/skills/spipe_doc_wiki_refactor.md` as the
operational checklist for stale docs, command names, process links, and
feature/layer expert cross-links. It does not replace the per-stage knowledge
update obligation; it catches accumulated drift after implementation has
stabilized and again before completion.

This is specified in [`pipeline_next_step_plan.md`](pipeline_next_step_plan.md)
(§"Runtime Process" step 5 and §"Design And Implementation Emphasis") and enforced
by the generator's drift check (`bin/simple llm-process-gen check`), which flags
missing, stale, or manually-edited generated docs and broken links.

New experts are copied from `template/feature_skill.md` / `template/layer_skill.md`
and then maintained as product knowledge changes, rather than regenerated.

## auto-research mapping

Karpathy's Auto-Research is a loop: hypothesize a change → edit → run a measurable
test → keep on improvement, revert on regression. The Simple equivalents are:

| Auto-Research concept | Simple artifact |
|-----------------------|-----------------|
| Goal (`program.md`) | The refined request summary + `doc/03_plan/agent_tasks/<feature>_<stage>.md` |
| Codebase | `src/` |
| Metric / judge (`prepare.py`) | Executable SPipe specs under `test/.../*_spec.spl` and generated/manual `doc/06_spec/.../*_spec.md` mirrors; `bin/simple test`, `bin/simple build check` |
| Keep / revert | `jj` working-copy snapshots (revert a regressing slice; main-only, no branches) |
| The loop driver | The `research → design → impl → verify → release` pipeline; periodic re-entry via `/spipe_loop` |

Note: `/spipe_loop`'s default continuous-check mode is currently a stub — only
`--daily-debug` is implemented (see [`.claude/skills/spipe_loop.md`](../../.claude/skills/spipe_loop.md)).
Until the orchestrator lands, the Auto-Research loop runs as the staged pipeline
driven turn-by-turn, with `bin/simple test` / `bin/simple build check` as the metric.

## see also

- [`pipeline_next_step_plan.md`](pipeline_next_step_plan.md) — lead-agent loop and knowledge-update step
- [`README.md`](README.md) — knowledge model, generator tool, drift alerts
- Karpathy LLM Wiki spec: https://gist.github.com/karpathy/442a6bf555914893e9891c11519de94f
- Karpathy Auto-Research: https://github.com/karpathy/autoresearch
