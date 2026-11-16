# Goal skill routing: CLI, read receipts and harness provider (2026-11-14)

Status: open. Slice D landed the registry `task_skills` table
(`doc/00_llm_process/knowledge_registry.sdn`) and the pure selector
`src/lib/common/llm/task_skill_selector.spl` (SKILL-001..008).

Landed 2026-11-15 (slice goalcli): `goal skills|start|status|resume` actions on
the harness CLI (`src/app/spipe_process_harness/main.spl`), pure decisions in
`src/lib/nogc_async_mut/spipe_process_harness/goal.spl`, one provider mapping
(`skill_provider_of`; the harness already normalizes kimi/unknown), persisted
receipt `.spipe/<goal>/skill_selection.sdn`, stale detection by registry digest.

Remaining:
- `goal skills --goal/--why/--check/--format` flags and `goal start "<text>"`
  free-text classification (plan 8.3) are not implemented; the task class is an
  explicit `--task`.
- SKILL-009, 012 (mandatory complete-read receipts, goal-change re-evaluation,
  provider-hook adapters) are unimplemented. `resume` detects only a changed
  registry digest, not a changed goal or touched component.
- No `kimi` adapters exist; every row has `kimi: disabled`. `setup` and `other`
  have no skill row (nothing real to point at).
- Pre-existing, unrelated: `test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`
  scenarios "should keep registry guide and process surfaces aligned" and
  "should route 2D and web rendering work to the GPU evidence knowledge" fail
  at origin/release/1.0.0 (file content assertions on `.codex/skills/sp_dev/SKILL.md`
  and rendering group docs) with and without this change.
