---
name: sp_dev
description: "SPipe dev entrypoint: refine a feature/bug/TODO into acceptance criteria, then continue through the SPipe pipeline."
---

# SP Dev -- SPipe Development Entrypoint

`/sp_dev` is the Codex entrypoint for the SPipe development workflow. The
standalone `/dev` Codex skill has been removed so development work routes
through the explicit SPipe namespace.

Use it for a feature, bug fix, refactor, or TODO that should start with SPipe
goal refinement and acceptance criteria, then continue through research, design,
SPipe specs, implementation, refactor, verification, and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Start with the SPipe dev agent instructions in `.claude/agents/spipe/dev.md`.
Use `.claude/skills/spipe.md` for SPipe test/spec conventions when the workflow
reaches specification and verification phases.

During the SPipe Refactor and Ship phases, run the doc/wiki refactor support
skill at `.claude/skills/spipe_doc_wiki_refactor.md` so stale docs, command
references, wiki-style process knowledge, and feature/layer expert links are
cleaned before completion.

For scenario-oriented work, the SPipe loop also includes generated manual
review. After specs are written or changed, generate the mirrored
`doc/06_spec/...` document and read it as a scenario manual. Update step
helpers, capture policy, inline/previous scenario expansion, and manual
visibility until the generated manual is good enough to use without opening the
source test. See `doc/07_guide/testing/sspec_scenario_manual.md`.

Run `sh scripts/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.

## LLM Fine-Tune Handoff

For SPipe LLM-backed app/server work, use the fine-tune registry commands under
`.spipe/llm-finetune-process/`. If an artifact exists but misses its target eval,
record the failed eval, create or link the retry attempt, and file remaining
retry/verification/safety/deployment work in `doc/08_tracking/todo/todo_db.sdn`
and `doc/08_tracking/feature_request/` before reporting the handoff state.
