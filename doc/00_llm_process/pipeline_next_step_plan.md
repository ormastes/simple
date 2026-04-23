# Pipeline Next Step Plan

## Goal

Make the LLM process repeatable: one lead agent refines a user request, loads the right feature and layer expert knowledge, delegates each pipeline step to the right skill expert or subagent, and updates the project knowledge after every phase.

## Current Inputs

- Pipeline skills: `skill_command/skills/pipe/<stage>/`
- Pipeline commands: `skill_command/command/`
- Feature experts: `feature_expert/<feature>/skill.md`
- Layer experts: `layer_expert/<layer>/skill.md`
- Initial expert templates: `template/feature_skill.md`, `template/layer_skill.md`
- Existing cooperative reference: `../guide/llm_cooperative_dev_phase.md`

## Runtime Process

1. Lead agent receives the user request and writes a refined request summary:
   - target feature, likely layers, intended pipeline stage, constraints, assumptions, and success criteria.
2. Lead agent loads matching expert knowledge:
   - feature experts from `feature_expert/<feature>/skill.md`
   - layer experts from `layer_expert/<layer>/skill.md`
   - stage skill from `skill_command/skills/pipe/<stage>/skill.md`
   - support skills from that stage directory when relevant.
3. Lead agent creates a next-step plan doc for the active stage:
   - recommended path: `doc/03_plan/agent_tasks/<feature>_<stage>.md`
   - include refined request, selected experts, delegated tasks, expected artifacts, verification commands, and knowledge-update targets.
4. Stage expert or subagents execute bounded work:
   - research: collect local/domain facts and requirement options.
   - design: produce architecture, detail design, UI design if needed, and system-test plan.
   - impl: implement from design while loading feature and layer expert knowledge before editing.
   - verify: check requirements, stubs, tests, architecture/design freshness, and required smoke commands.
   - release: update version, changelog, commit/tag, and push only after confirmation.
5. After each stage, update knowledge:
   - append or refresh links in affected `feature_expert/<feature>/skill.md`
   - append or refresh links in affected `layer_expert/<layer>/skill.md`
   - update next-step plan status and handoff notes
   - update `skill_command/` only when reusable project-neutral process knowledge changed.

## Generator Tool Plan

Add a project tool named `llm-process-gen`.

Recommended commands:

```bash
bin/simple llm-process-gen check
bin/simple llm-process-gen generate
bin/simple llm-process-gen generate --force
```

Responsibilities:

- Generate skill, command, and subagent files for Claude, Codex, and Gemini CLI from a canonical process manifest.
- Generate project-process copies under `doc/00_llm_process/skill_command/`.
- Generate feature and layer expert skeletons by copying templates from `doc/00_llm_process/template/`.
- Generate subagent docs that hide MCP/tool details behind task-oriented instructions, while retaining tool metadata in `tools.sdn`.
- Check drift before writing:
  - missing generated file
  - stale generated file
  - manually changed generated file
  - broken documented link
  - source template or manifest changed while generated docs are stale.
- Alert the user when generated docs changed:
  - tell the user `skill_command/` should be regenerated to apply the process changes.
  - require `--force` to overwrite generated files that no longer match their recorded generated hash.

## Canonical Manifest

Create `doc/00_llm_process/llm_process_manifest.sdn` as the source of truth.

Minimum tables:

```text
skills |id, owner, stage, trigger, template, generated_path|
commands |id, owner, trigger, generated_path|
subagents |id, owner, stage, generated_path|
tools |id, type, name, purpose|
expert_routes |signal, feature_expert, layer_expert, stage|
```

Rules:

- `owner` is `claude`, `codex`, or `gemini`.
- `type` is `cli` or `mcp`.
- `trigger` uses `/name` for Claude and Gemini, `$name` for Codex.
- Generated files include a stable generated marker or hash so drift can be detected.

## Subagent Routing

Lead agent should delegate only bounded work. Suggested routing:

- Request refinement: lead agent only.
- Feature discovery: feature expert subagent.
- Layer impact analysis: layer expert subagent.
- Stage execution plan: pipeline stage expert.
- Implementation slices: worker subagents by layer or module with disjoint write sets.
- Verification: verifier subagent can run in parallel after implementation starts, but final readiness stays with the lead agent.

Subagent task packet:

```text
request:
feature:
layers:
stage:
loaded_experts:
constraints:
expected_artifacts:
allowed_write_scope:
verification:
return_format:
```

## Design And Implementation Emphasis

Design and implementation must load feature and layer expert knowledge before making decisions:

- design loads feature expert, all affected layer experts, `pipe/design/skill.md`, and support design skills such as `pipe/design/arch/skill.md`.
- impl loads feature expert, all affected layer experts, `pipe/impl/skill.md`, and support implementation skills such as `pipe/impl/refactor/skill.md`.
- both stages must update expert skills when they create new docs, change contracts, discover constraints, or add verification requirements.

## Acceptance Criteria

- README documents the lead-agent process, generator tool, drift alerts, and force regeneration.
- Templates explain that new experts are copied from `template/` and updated as product knowledge changes.
- Generator plan defines skill, command, and subagent generation for Claude, Codex, and Gemini CLI.
- Every generated/copied skill has links to related process docs and a `tools.sdn` with `id` and `type`.
