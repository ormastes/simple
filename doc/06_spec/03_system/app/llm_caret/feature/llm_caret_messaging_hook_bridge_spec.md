# llm_caret_messaging_hook_bridge_spec

> Verifies the llm caret messaging hook bridge behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_caret_messaging_hook_bridge_spec

Verifies the llm caret messaging hook bridge behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret messaging hook bridge behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret durable hook bridge

#### normalizes lifecycle events for Claude Codex and Gemini

- Verify: normalizes lifecycle events for Claude Codex and Gemini
   - Expected: normalize_hook_event("claude", "PermissionRequest").lifecycle_state equals `waiting_input`
   - Expected: normalize_hook_event("codex", "turn/completed").lifecycle_state equals `completed`
   - Expected: normalize_hook_event("gemini", "AfterAgent").lifecycle_state equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-008 REQ-LLM-MSG-013 REQ-LLM-MSG-014
step("Verify: normalizes lifecycle events for Claude Codex and Gemini")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_hook_event("claude", "PermissionRequest").lifecycle_state).to_equal("waiting_input")
expect(normalize_hook_event("codex", "turn/completed").lifecycle_state).to_equal("completed")
expect(normalize_hook_event("gemini", "AfterAgent").lifecycle_state).to_equal("completed")
```

</details>

<details>
<summary>Advanced: advances a correlated task and publishes truthful room updates</summary>

#### advances a correlated task and publishes truthful room updates

- Verify: advances a correlated task and publishes truthful room updates
   - Expected: store.create_room(hook_room()).ok is true
   - Expected: store.put_agent_binding(binding).ok is true
   - Expected: store.append_message(message.message, "origin-idempotency").ok is true
   - Expected: store.put_task(task.task).ok is true
- Reconstruct bounded canonical context for the provider hook
   - Expected: hook_room_context(store, "task-origin", "other-room", "builder") equals ``
   - Expected: store.enqueue_hook_event("hook-running", "claude", "PostToolUse", "{}", 2).ok is true
   - Expected: store.enqueue_hook_event("hook-complete", "claude", "Stop", "{}", 3).ok is true
   - Expected: drained.0 equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: drained.1 equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: tasks[0].state equals `TaskState.Completed`
   - Expected: store.task_events("task-origin").len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.message_history("hooks", 0, 10).len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipts[receipts.len() - 1].state equals `ReceiptState.Handled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-008 REQ-LLM-MSG-013 REQ-LLM-MSG-014
step("Verify: advances a correlated task and publishes truthful room updates")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var store = PureSqlMessagingStore.open_memory()
expect(store.create_room(hook_room()).ok).to_equal(true)
val binding = AgentBinding(binding_id: messaging_id("agent_binding", "hook-binding"),
    room_id: messaging_id("room", "hooks"), agent_id: messaging_id("agent", "builder"),
    handler: AgentHandler.Main, session_policy: "persistent_per_room",
    trigger_policy: "room", update_policy: "milestones", context_policy: "bounded",
    permissions: [])
expect(store.put_agent_binding(binding).ok).to_equal(true)
val message = prepare_message("origin", "workspace", "hooks", 1, "human", "",
    MessageOrigin.Human, "build it", "", "", "corr", "", 0, 1)
expect(store.append_message(message.message, "origin-idempotency").ok).to_equal(true)
val task = create_task("task-origin", "origin", "builder", "build it", 1)
expect(store.put_task(task.task).ok).to_equal(true)
step("Reconstruct bounded canonical context for the provider hook")
val context = hook_room_context(store, "task-origin", "hooks", "builder")
expect(context).to_contain("[#origin] build it")
expect(hook_room_context(store, "task-origin", "other-room", "builder")).to_equal("")
expect(store.enqueue_hook_event("hook-running", "claude", "PostToolUse", "{}", 2).ok).to_equal(true)
expect(store.put_hook_correlation(StoredHookCorrelation(event_id: "hook-running",
    task_id: "task-origin", room_id: "hooks", agent_id: "builder")).ok).to_equal(true)
expect(store.enqueue_hook_event("hook-complete", "claude", "Stop", "{}", 3).ok).to_equal(true)
expect(store.put_hook_correlation(StoredHookCorrelation(event_id: "hook-complete",
    task_id: "task-origin", room_id: "hooks", agent_id: "builder")).ok).to_equal(true)
val drained = drain_hook_events(store, 10)
expect(drained.0).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(drained.1).to_equal(0)  # oracle: pinned constant asserted by this scenario
val tasks = store.tasks()
expect(tasks[0].state).to_equal(TaskState.Completed)
expect(store.task_events("task-origin").len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(store.message_history("hooks", 0, 10).len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
val receipts = store.receipts("origin")
expect(receipts[receipts.len() - 1].state).to_equal(ReceiptState.Handled)
store.close()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4a43efab78e3f8aa8981705abd4a9fc9527f9cdcaec1a29c72d1fdee9084230`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4a43efab78e3f8aa8981705abd4a9fc9527f9cdcaec1a29c72d1fdee9084230`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4a43efab78e3f8aa8981705abd4a9fc9527f9cdcaec1a29c72d1fdee9084230`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_hook_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
