# Pipeline Next Step Plan

## Goal

Make the LLM process repeatable: one lead agent refines a user request, loads the right feature and layer expert knowledge, delegates each pipeline step to the right skill expert or subagent, and updates the project knowledge after every phase.

The next process target is LLM pair programming: the lead agent keeps the driver role for user intent, sequencing, and final synthesis, while feature, layer, and pipeline experts act as navigators that challenge assumptions, supply context, draft plans, and update durable knowledge.

## Current Inputs

- Pipeline skills: `skill_command/skills/pipe/<stage>/`
- Pipeline commands: `skill_command/command/`
- Feature experts: `feature_expert/<feature>/skill.md`
- Layer experts: `layer_expert/<layer>/skill.md`
- Initial expert templates: `template/feature_skill.md`, `template/layer_skill.md`
- Existing cooperative reference: `../guide/llm_cooperative_dev_phase.md`

## Pair Programming Research Notes

Classic pair programming separates immediate execution from strategic navigation: the driver handles concrete edits while the navigator reviews, reasons about design, and looks ahead. Reported benefits center on knowledge transfer, shared review, and reduced defects, but the benefit depends on active role clarity rather than two people merely touching the same task.

For LLM pair programming, use the same pattern with explicit agents:

- Lead agent: driver for request refinement, sequencing, conflict resolution, final plan/doc merge, and user communication.
- Feature expert agent: navigator for product/feature history, requirements, artifacts, and feature-specific risks.
- Layer expert agent: navigator for source-layer contracts, affected modules, test obligations, and cross-layer coupling.
- Pipeline stage expert: navigator for the active stage contract, artifact checklist, and phase-specific quality gates.

References:

- Pair programming driver/navigator role summary: https://www.techtarget.com/searchsoftwarequality/definition/Pair-programming
- Pair programming knowledge-transfer research: https://www.sciencedirect.com/science/article/pii/S1071581914001207
- Distributed pair-programming systematic review: https://pmc.ncbi.nlm.nih.gov/articles/PMC9930723/
- Human-AI pair-programming evaluation: https://arxiv.org/abs/2306.05153

## Runtime Process

1. Lead agent receives the user request and writes a refined request summary:
   - target feature, likely layers, intended pipeline stage, constraints, assumptions, and success criteria.
2. Lead agent starts an LLM pair-programming loop:
   - load the stage skill from `skill_command/skills/pipe/<stage>/skill.md`
   - spawn or assign feature expert subagents for each likely `feature_expert/<feature>/skill.md`
   - spawn or assign layer expert subagents for each likely `layer_expert/<layer>/skill.md`
   - ask each expert to return context, risks, required docs, verification expectations, and update targets.
3. Lead agent creates a next-step plan doc for the active stage:
   - recommended path: `doc/03_plan/agent_tasks/<feature>_<stage>.md`
   - include refined request, selected experts, expert findings, delegated tasks, expected artifacts, verification commands, and knowledge-update targets.
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

## Research And Design Pairing

Research and design must use feature and layer expert subagents before finalizing their stage outputs.

Research flow:

1. Lead agent drafts the research plan and identifies candidate feature/layer experts from request text, file paths, prior docs, and source ownership.
2. Feature expert subagent reads its `feature_expert/<feature>/skill.md`, finds existing research/requirements/plans, and drafts feature-specific research updates.
3. Layer expert subagents read their `layer_expert/<layer>/skill.md`, inspect local layer docs/source references, and draft layer impact notes.
4. Research stage expert merges these drafts into:
   - `doc/01_research/local/<feature>.md`
   - `doc/01_research/domain/<feature>.md` when external/domain knowledge is needed
   - `doc/02_requirements/feature/<feature>_options.md`
   - `doc/02_requirements/nfr/<feature>_options.md`
5. Feature and layer expert agents update their own `skill.md` files with new links, constraints, decisions pending user selection, and known verification needs.

Design flow:

1. Lead agent loads final requirements, feature experts, affected layer experts, `pipe/design/skill.md`, and support design skills such as `pipe/design/arch/skill.md`.
2. Feature expert subagent drafts feature-level design context: user-visible behavior, requirement links, artifact list, and open risks.
3. Layer expert subagents draft layer-level design context: public contracts, data flow, cross-layer boundaries, test surfaces, performance or startup impact, and smoke-check needs.
4. Design stage expert merges these drafts into:
   - `doc/04_architecture/<feature>.md`
   - `doc/05_design/<feature>.md`
   - `doc/03_plan/sys_test/<feature>.md`
   - `doc/03_plan/agent_tasks/<feature>_impl.md`
   - `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` when system tests are ready.
5. Feature and layer expert agents update their own `skill.md` files with new design links, changed contracts, affected modules, test obligations, and handoff notes for implementation.

Research and design outputs are drafts until the lead agent reconciles conflicts between experts and records the final merged plan.

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
- Feature discovery and knowledge updates: feature expert subagent.
- Layer impact analysis and knowledge updates: layer expert subagent.
- Stage execution plan and merge draft: pipeline stage expert.
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

Expert return format:

```text
expert_id:
source_skill:
relevant_links:
findings:
risks:
required_artifacts:
verification:
doc_updates:
open_questions:
```

## Design And Implementation Emphasis

Design and implementation must load feature and layer expert knowledge before making decisions:

- design loads feature expert, all affected layer experts, `pipe/design/skill.md`, and support design skills such as `pipe/design/arch/skill.md`.
- impl loads feature expert, all affected layer experts, `pipe/impl/skill.md`, and support implementation skills such as `pipe/impl/refactor/skill.md`.
- research and design must spawn or assign expert subagents before finalizing research, requirements, architecture, design, or plan docs.
- impl must retrieve the latest feature and layer expert knowledge before editing and must update it when implementation changes contracts, module ownership, or verification obligations.
- each expert subagent updates its own `skill.md` when it creates new docs, changes links, discovers constraints, or adds verification requirements.

## Acceptance Criteria

- README documents the lead-agent process, generator tool, drift alerts, and force regeneration.
- Templates explain that new experts are copied from `template/` and updated as product knowledge changes.
- Generator plan defines skill, command, and subagent generation for Claude, Codex, and Gemini CLI.
- Every generated/copied skill has links to related process docs and a `tools.sdn` with `id` and `type`.
- Research and design stage docs require feature expert and layer expert subagent drafts before the lead agent merges final outputs.
- Feature and layer expert skills are updated by their expert agents when research, plan, design, or implementation knowledge changes.
