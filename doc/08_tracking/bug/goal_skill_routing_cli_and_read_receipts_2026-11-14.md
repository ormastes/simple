# Goal skill routing: CLI, read receipts and harness provider (2026-11-14)

Status: open. Slice D landed the registry `task_skills` table
(`doc/00_llm_process/knowledge_registry.sdn`) and the pure selector
`src/lib/common/llm/task_skill_selector.spl` (SKILL-001..008).

Remaining:
- `simple goal start|skills|status|resume` CLI (plan 8.3) is absent; nothing
  calls `select_goal_skills` yet. Unblock: route through the SPipe process
  harness, not a parallel engine.
- SKILL-009..012 (mandatory complete-read receipts, persisted selection for
  resume/compaction, goal-change re-evaluation, provider-hook adapters) are
  unimplemented.
- `src/lib/nogc_async_mut/spipe_process_harness/**` still normalizes only
  codex/claude/gemini; the selector's `SkillProvider` (adds Kimi, Unknown) must
  be unified with it once the CLI lands.
- No `kimi` adapters exist; every row has `kimi: disabled`. `setup` and `other`
  have no skill row (nothing real to point at).
- Pre-existing, unrelated: `test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`
  scenarios "should keep registry guide and process surfaces aligned" and
  "should route 2D and web rendering work to the GPU evidence knowledge" fail
  at origin/release/1.0.0 (file content assertions on `.codex/skills/sp_dev/SKILL.md`
  and rendering group docs) with and without this change.
