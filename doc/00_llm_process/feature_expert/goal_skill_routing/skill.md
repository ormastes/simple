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
- Provider is a typed enum local to the selector; the SPipe process harness
  provider normalization is NOT touched (follow-up).

## Tests

`test/01_unit/lib/common/llm/task_skill_selector_spec.spl` (SKILL-001..008) and
the real-registry scenarios in
`test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`.

## Not done

`simple goal ...` CLI, mandatory read receipts, SKILL-009..012: see
`doc/08_tracking/bug/goal_skill_routing_cli_and_read_receipts_2026-11-14.md`.
