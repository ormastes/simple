# llm process

## pipeline process

One lead agent owns the user conversation. It refines the request, identifies the target feature and layers, loads the relevant expert knowledge, and delegates bounded work to pipeline skill experts or subagents.

The next process direction is LLM pair programming: the lead agent drives request refinement and final synthesis, while feature experts, layer experts, and pipeline stage experts act as navigators that draft research, plans, risks, and knowledge updates.

Default feature pipeline: `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`.

For the next implementation step, use [pipeline_next_step_plan.md](pipeline_next_step_plan.md). The plan defines how to load feature expert knowledge, layer expert knowledge, and pipeline-stage skills before generating the next step plan doc.

## knowledge model

- Project experts live at `project_expert/<project-or-subproject>/skill.md`.
- Feature experts live at `feature_expert/<feature>/skill.md`.
- Layer experts live at `layer_expert/<layer>/skill.md`.
- Domain experts live at `domain_expert/<domain>/skill.md`.
- Tool experts live at `tool_expert/<tool>/skill.md`.
- Initial expert templates live in `template/`.
- Reusable project-neutral skill and command knowledge lives in `skill_command/`.

When a new feature or layer expert is needed, copy the matching template from `template/`, create the expert directory, and update the new `skill.md` with links to the relevant project docs and source paths. When product knowledge changes during research, design, implementation, verification, or release, update the affected feature and layer expert skills.

SPipe also has an explicit doc/wiki refactor checkpoint in Refactor and Ship.
Use `.claude/skills/spipe_doc_wiki_refactor.md` to fix stale docs, command
names, process links, and feature/layer expert cross-links, then record the
updated paths in `.spipe/<feature>/state.md`.

This expert tree plus the self-healing update step is Simple's realization of the LLM Wiki and Auto-Research patterns — see [llm_wiki_and_auto_research.md](llm_wiki_and_auto_research.md) for the concept mapping.

## SPipe project

Reusable SPipe process assets live in the standalone SPipe project from
`https://github.com/ormastes/Spipe.git`.

This host repository keeps two mounts:

- `examples/spipe`: the example SPipe project submodule.
- `.spipe/spipe`: the compatibility submodule mount used by existing setup
  scripts and links.

The host-local `.spipe/doc` link points to this repository's configured process
doc root, `doc/00_llm_process`. SPipe's generic default is `doc/llm_process`,
but this repository keeps the current `doc/00_llm_process` path.

The host setup script initializes both SPipe submodules, refreshes
`.spipe/spipe_project` and `.spipe/doc`, and links reusable expert roots into
this repository:

```bash
sh scripts/setup-spipe-submodule.shs
```

On Windows, run the PowerShell setup script from the submodule:

```powershell
powershell -ExecutionPolicy Bypass -File .spipe\spipe\scripts\setup-spipe-links.ps1
```

The link setup preserves existing host-owned directories unless `--force` is
passed. In this repository, `skill_command/`, `spipe/`, `template/`,
`project_expert/`, `domain_expert/`, and `tool_expert/` are linked from the
submodule. Host-specific subproject expert links are kept under `.spipe/` by
`.spipe/subproject_links.sdn` so they do not write through the shared
`project_expert/` symlink into the reusable SPipe project.

## generator tool

Use the generator to keep copied LLM process files reproducible from the manifest and source skill files:

```bash
bin/simple llm-process-gen check
bin/simple llm-process-gen check --json
bin/simple llm-process-gen list
bin/simple llm-process-gen list --owner codex
bin/simple llm-process-gen list --mode tools_sdn
bin/simple llm-process-gen list --stage sync
bin/simple llm-process-gen generate
bin/simple llm-process-gen generate --force
```

The tool should generate skills, commands, and subagent docs for Claude, Codex, and Gemini CLI. Subagent docs should hide MCP details behind task-oriented instructions; tool metadata stays in `tools.sdn` with `id` and `type`.

`check` alerts the user when generated docs drift from templates or the manifest. `list` prints manifest-managed outputs and can filter by owner, mode, or stage. When generated docs change, the LLM should notify the user that `skill_command/` should be regenerated. `generate --force` regenerates marker-managed outputs after the user accepts the overwrite.

Skeleton records create feature and layer expert files only when the target is missing. Existing skeleton targets are durable knowledge files and are not overwritten by `generate` or `generate --force`.

`generated_files.mode` is validated. Allowed values are:

- `managed`: copy the source text into a marker-managed output
- `gemini_toml_skill`: render a Gemini TOML command or skill as markdown
- `tools_sdn`: render standard skill `tools.sdn` metadata from the manifest
- `claude_lib_tools_sdn`: render Claude helper skill `tools.sdn` metadata
- `skeleton`: create the target only when missing, then leave later edits intact

## skills & commands

Claude skill copies live under `skill_command/skills/pipe/<stage>/` and are grouped by pipeline stage. Each primary stage has direct `skill.md` and `tools.sdn` files; support skills live in subfolders with their own `skill.md` and `tools.sdn`. Tool rows include `id` and `type` where type is `cli` or `mcp`.
Pipeline-only Claude command copies live under `skill_command/command/`.

Additional extracted skills:

- Codex: `skill_command/skills/codex/<skill>/skill.md`
- Gemini: `skill_command/skills/gemini/<skill>/skill.md`
- Claude helpers: `skill_command/skills/claude/lib/<skill>/skill.md`
- Project experts: `project_expert/<project-or-subproject>/skill.md`
- Feature experts: `feature_expert/<feature>/skill.md`
- Layer experts: `layer_expert/<layer>/skill.md`
- Domain experts: `domain_expert/<domain>/skill.md`
- Tool experts: `tool_expert/<tool>/skill.md`
- Templates: `template/feature_skill.md`, `template/layer_skill.md`

Every extracted skill folder includes `tools.sdn` with `tools |id, type, name, purpose|`; `type` is `cli` or `mcp`.


Stage support skill grouping:

- Research: `research/skill.md`, `research/research_codex/`
- Design: `design/skill.md`, `design/arch/`, `design/gemini_ui_design/`, `design/theme_sync/`, `design/ui/`
- Implementation: `impl/skill.md`, `impl/dev/`, `impl/refactor/`, `impl/spipe_loop/`, `impl/stitch/`, `impl/sync/`
- Documentation/wiki refactor checkpoint: `.claude/skills/spipe_doc_wiki_refactor.md` during SPipe Refactor and Ship
- Verification: `verify/skill.md`, `verify/bug_review/`
- Release: `release/skill.md`, `release/mail/`, `release/repo_and_pull_req/`

| Skill | Command | Copied skill file | Copied command file | Source skill file | Source command file |
|-------|---------|-------------------|---------------------|-------------------|---------------------|
| research | `/research` | `skill_command/skills/pipe/research/skill.md` | `skill_command/command/research.md` | `.claude/skills/research.md` | `.claude/commands/research.md` |
| design | `/design` | `skill_command/skills/pipe/design/skill.md` | `skill_command/command/design.md` | `.claude/skills/design.md` | `.claude/commands/design.md` |
| impl | `/impl` | `skill_command/skills/pipe/impl/skill.md` | `skill_command/command/impl.md` | `.claude/skills/impl.md` | `.claude/commands/impl.md` |
| verify | `/verify` | `skill_command/skills/pipe/verify/skill.md` | `skill_command/command/verify.md` | `.claude/skills/verify.md` | `.claude/commands/verify.md` |
| release | `/release` | `skill_command/skills/pipe/release/skill.md` | `skill_command/command/release.md` | `.claude/skills/release.md` | `.claude/commands/release.md` |
