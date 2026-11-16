# Goal skill routing feature expert

## Role

Owns goal-start task-skill selection: the `task_skills` table in
`doc/00_llm_process/knowledge_registry.sdn` (registry version 2) and the pure
selector `src/lib/common/llm/task_skill_selector.spl`. Plan: sections 8 and 9
(`SKILL-001`..`SKILL-012`) of the 2026-11-14 traceability/SPipe/skills plan.

## Contract

- One registry, no competing inventory: rows live beside `feature_routes` and
  `layer_routes`; existing route consumers ignore the new section.
- Rows exist only for skills whose files exist (Claude `.claude/skills/*.md`,
  Codex `.codex/skills/*/SKILL.md`, Gemini `.gemini/commands/*.toml`, canonical
  `.agents/skills` or Codex path). `disabled` marks a missing adapter. Kimi is
  `disabled` everywhere: no Kimi skill directory exists. `setup` and `other`
  have no row and select as `skill-missing`.
- `select_goal_skills(registry_text, task_class, provider)` is pure (no I/O; the
  caller reads the file) and fail closed: the whole table is validated first
  (malformed row, duplicate id, ambiguous alias, ambiguous task class, missing
  or cyclic dependency), then the class is resolved; a disabled adapter on the
  primary or any transitive dependency is `not-enabled-for-provider`. An
  `Unknown` provider activates nothing and returns `FallbackAsk` candidates.
- `goal_skill_selection_receipt` records registry version and SHA-256 digest.
- Providers are unified by ONE mapping: the harness `normalize_provider` is the
  only text parser; `skill_provider_of(Provider) -> SkillProvider` in
  `src/lib/nogc_async_mut/spipe_process_harness/goal.spl` maps onto the
  selector enum (`src/lib/common` cannot import `nogc_async_mut`, so both enums
  stay and the mapping lives on the harness side).

## Goal CLI (harness `goal` action)

`bin/simple run src/app/spipe_process_harness/main.spl goal <skills|start|status|resume> ...`
- `skills --task <class> [--provider <p>] [--registry <path>]` prints the
  `GoalSkillSelectionV1` receipt text; writes nothing.
- `start --goal <id> --task <class> --provider <p>` additionally writes the
  receipt to `.spipe/<id>/skill_selection.sdn` only for a `Selected` outcome.
- `status --goal <id>` prints the stored receipt; `resume --goal <id>`
  compares the stored `registry_digest` with the current registry's SHA-256.
- Exit codes (`goal_exit_code`): 0 selected/fresh, 1 rejected (typed
  `error=<kind>:<subject>` printed, nothing written; an unknown task class prints
  `error=unknown-task-class:<x>`), 3 ask (unknown or blank provider: candidates
  listed, nothing written, never a silent default), 4 stale, 5 receipt missing,
  6 receipt unreadable.
- Pure decisions (`parse_goal_skills_request`, `plan_goal_skills`,
  `evaluate_goal_resume`) live in `goal.spl`; `main.spl` only does file I/O.
- Spec: `test/01_unit/app/spipe_process_harness/spipe_goal_cli_spec.spl`
  (SKILL-002/004/005/010/011).

## Tests

`test/01_unit/lib/common/llm/task_skill_selector_spec.spl` (SKILL-001..008) and
the real-registry scenarios in
`test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`.

## Not done

Mandatory complete-read receipts, goal-change re-evaluation, provider-hook
adapters (SKILL-009, 012 and part of 011): see
`doc/08_tracking/bug/goal_skill_routing_cli_and_read_receipts_2026-11-14.md`.
