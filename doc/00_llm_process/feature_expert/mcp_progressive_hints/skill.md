# Feature Expert: MCP Progressive Hints

## Role

Own the progressive-hint policy for Simple MCP capabilities: when a tool response
carries full guidance, a brief tip, a corrective mini-hint, or nothing. Source plan:
`simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` §7 (MCP
capability discovery and progressive hints) and the Hints row of §9.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Source (pure policy): `src/lib/common/llm/hint_policy.spl`
- Spec: `test/01_unit/lib/common/llm/hint_policy_spec.spl`
- Remaining work: [doc/08_tracking/bug/mcp_progressive_hints_wiring_missing_2026-11-14.md](../../../08_tracking/bug/mcp_progressive_hints_wiring_missing_2026-11-14.md)
- Sibling pure LLM policies: `src/lib/common/llm/knowledge_selector.spl`, `output_gate.spl`

## Current contract (slice B, 2026-11-14)

`decide_hint(state: HintState, event: HintEvent, now: HintTimestamp, version: HintSchemaVersion) -> (HintLevel, HintState)`
is pure: no I/O, no globals, no clock read. The caller owns one `HintState` per
session x capability (x version) and passes `now`.

- `HintLevel`: `Full` | `Brief` | `Corrective` | `Quiet`. `Corrective` is the plan's
  "targeted corrective mini-hint" row (<=100 tokens) and is kept distinct from
  `Brief` so the wiring slice can render it differently.
- `HintEvent`: `ToolSucceeded` | `ToolFailed` (includes malformed requests; never
  counts as success) | `HelpRequested`.
- State fields: `seen_count`, `success_count` (`HintCount`), `last_hint_time`
  (`HintTimestamp?`), `last_version` (`HintSchemaVersion?`), `recent_errors`
  (`HintErrorWindow`: failure instants since the last success, capped at 5),
  `suppressed_until` (`HintTimestamp?`).

Decision order for a non-help event: suppressed -> Quiet; first exposure -> Full;
5th failure since last success -> Full (errors cleared, fires once); 3 errors with
`now - t < 600s` -> Corrective (suppressed for 600s, fires once); version changed ->
Full; `now - last_hint_time >= 30 days` -> Full; second exposure -> Brief; else Quiet.
`last_hint_time` / `last_version` move only when a hint is actually emitted, so a
version change during suppression fires once suppression ends. Help is always Full,
ignores suppression, and does not count as a use or success.

## HINT fixture ID mapping (plan §9.1 defines only the range)

| ID | Meaning | Status |
| --- | --- | --- |
| HINT-001 | first use -> full | spec |
| HINT-002 | second use -> brief | spec |
| HINT-003 | third+ successful use -> quiet | spec |
| HINT-004 | 3 errors in 10 min -> corrective, once | spec |
| HINT-005 | 30 days since last hint -> full rehint, once | spec |
| HINT-006 | schema/command version change -> full rehint, once | spec |
| HINT-007 | explicit help overrides suppression; suppression keeps quiet | spec |
| HINT-008 | 5 failures -> rehint once; failures never success; session isolation | spec |
| HINT-009 | every hint references a registered command/tool | open (bug record) |
| HINT-010 | CI catches stale hints after renames | open (bug record) |

## Known gaps

- "30 days of inactivity" is measured from the last hint (no last-use field in the
  plan's six-field state).
- "3 matching errors" counts all failures; no error identity is modelled.
- No MCP wiring yet (`simple_help`, `simple_capabilities`, `simple_hint_status`,
  `simple://` resources, prompts). See the bug record.

## Verification

```bash
bin/simple test test/01_unit/lib/common/llm/hint_policy_spec.spl
bin/simple lint src/lib/common/llm/hint_policy.spl
```

## Update Rule

When MCP wiring, provider hooks or the stale-hint CI land, update this file with the
new entry points and flip HINT-009/010 status.
