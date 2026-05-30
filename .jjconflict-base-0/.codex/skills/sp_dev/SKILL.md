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

Run `sh scripts/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.
