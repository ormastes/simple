# session_store_spec

> Purpose: Prove that assistant session store.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# session_store_spec

Purpose: Prove that assistant session store.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp/assistant/session_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that assistant session store.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### assistant session store

#### rejects non-object root inputs and generates missing session ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects non-object root inputs and generates missing session ids
- Verify: rejects non-object root inputs and generates missing session ids
   - Expected: session.session_id.starts_with("assistant-") is true
   - Expected: session.name equals `Generated Session`
   - Expected: session.summary equals `generate an id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-object root inputs and generates missing session ids")
step("Verify: rejects non-object root inputs and generates missing session ids")
# @req: REQ-APP-MCP-001
val root = test_root("input")

expect(assistant_store_create_session(root, json_parse("1"))).to_be_nil()
expect(assistant_store_append_event(root, json_parse("1"))).to_be_nil()
expect(assistant_store_create_child_task(root, json_parse("1"))).to_be_nil()

val created = assistant_store_create_session(
    root,
    json_parse(r"""{"name":"Generated Session","prompt":"generate an id"}""")
)
match created:
    case Some(session):
        expect(session.session_id.starts_with("assistant-")).to_equal(true)
        expect(session.name).to_equal("Generated Session")
        expect(session.summary).to_equal("generate an id")
    case nil:
        fail("valid object session without id should be created")
```

</details>

#### normalizes signal events without hanging and preserves wake reason

- normalizes signal events without hanging and preserves wake reason
- Verify: normalizes signal events without hanging and preserves wake reason
   - Expected: session.last_event_kind equals `signal_event`
   - Expected: session.last_signal equals `wake`
   - Expected: session.last_event_detail equals `wake payload`
   - Expected: session.event_count equals `1`
   - Expected: session.last_event_kind equals `signal_event`
   - Expected: session.last_signal equals `wake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes signal events without hanging and preserves wake reason")
step("Verify: normalizes signal events without hanging and preserves wake reason")
val root = test_root("signal")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-signal-1","name":"Signal Session","summary":"signal","objective":"signal","prompt":"signal","mode":"proactive","state":"running"}""")
)

val appended = assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-signal-1","kind":"signal","message":"wake payload","signal":"wake","timestamp_ms":1000,"event_id":"event-signal-1"}""")
)
match appended:
    case Some(session):
        expect(session.last_event_kind).to_equal("signal_event")
        expect(session.last_signal).to_equal("wake")
        expect(session.last_event_detail).to_equal("wake payload")
        expect(session.event_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
    case nil:
        fail("assistant signal event append should return session")

val loaded = assistant_store_load_session(root, "assistant-signal-1")
match loaded:
    case Some(session):
        expect(session.last_event_kind).to_equal("signal_event")
        expect(session.last_signal).to_equal("wake")
    case nil:
        fail("assistant signal session should load")
```

</details>

#### creates, loads, updates, and tracks child metadata

- creates, loads, updates, and tracks child metadata
- Verify: creates, loads, updates, and tracks child metadata
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.name equals `Assistant Core`
   - Expected: session.summary equals `build the store`
   - Expected: session.state equals `running`
   - Expected: listed.len() equals `1`
   - Expected: session.event_count equals `1`
   - Expected: session.last_event_kind equals `note`
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `state`
   - Expected: session.last_signal equals `pause`
   - Expected: session.event_count equals `3`
   - Expected: session.last_event_kind equals `child_task`
   - Expected: session.children.len() equals `1`
   - Expected: session.children[0] equals `assistant-child-1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `3`
   - Expected: session.children.len() equals `1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates, loads, updates, and tracks child metadata")
step("Verify: creates, loads, updates, and tracks child metadata")
val root = test_root("roundtrip")
val created = assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","name":"Assistant Core","summary":"build the store","objective":"build the store","prompt":"build the store","mode":"proactive","state":"running"}""")
)
match created:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-1")
        expect(session.name).to_equal("Assistant Core")
        expect(session.summary).to_equal("build the store")
        expect(session.state).to_equal("running")
    case nil:
        fail("assistant session should be created")

val listed = assistant_store_list_sessions(root)
expect(listed.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement

val appended = assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","kind":"note","message":"first event","signal":""}""")
)
match appended:
    case Some(session):
        expect(session.event_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(session.last_event_kind).to_equal("note")
    case nil:
        fail("assistant event append should return session")

val updated = assistant_store_update_state(root, "assistant-core-1", "paused", "pause")
match updated:
    case Some(session):
        expect(session.state).to_equal("paused")
        expect(session.event_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
        expect(session.last_event_kind).to_equal("state")
        expect(session.last_signal).to_equal("pause")
    case nil:
        fail("assistant state update should return session")

val child = assistant_store_create_child_task(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","objective":"inspect subgraph","owner_kind":"assistant","resource_policy":"bounded","child_session_id":"assistant-child-1","status":"queued"}""")
)
match child:
    case Some(session):
        expect(session.event_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
        expect(session.last_event_kind).to_equal("child_task")
        expect(session.children.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(session.children[0]).to_equal("assistant-child-1")
        expect(session.child_tasks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(session.child_tasks[0].child_session_id).to_equal("assistant-child-1")
    case nil:
        fail("assistant child task creation should return session")

val loaded = assistant_store_load_session(root, "assistant-core-1")
match loaded:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-1")
        expect(session.state).to_equal("paused")
        expect(session.event_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
        expect(session.children.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(session.child_tasks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(session.child_tasks[0].child_session_id).to_equal("assistant-child-1")
    case nil:
        fail("assistant session should load after updates")
```

</details>

#### writes dashboard-compatible session and timeline files

- writes dashboard-compatible session and timeline files
- Verify: writes dashboard-compatible session and timeline files
   - Expected: session.session_id equals `assistant-core-compat`
   - Expected: json_to_string(json_object_get(session_value, "id")) equals `assistant-core-compat`
   - Expected: json_to_string(json_object_get(session_value, "state")) equals `running`
   - Expected: json_get_type(json_object_get(session_value, "updated_at")) equals `number`
   - Expected: json_get_type(json_object_get(session_value, "child_tasks")) equals `array`
   - Expected: json_array_length(json_object_get(session_value, "child_tasks")) equals `1`
   - Expected: non_empty_lines_count(timeline_jsonl) equals `3`
   - Expected: json_to_string(json_object_get(first_line, "kind")) equals `note`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes dashboard-compatible session and timeline files")
step("Verify: writes dashboard-compatible session and timeline files")
val root = test_root("compat")
val created = assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","name":"Compat Session","summary":"compatibility","objective":"compatibility","prompt":"compatibility","mode":"proactive","state":"running"}""")
)
match created:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-compat")
    case nil:
        fail("compat session should be created")

assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","kind":"note","message":"compat event","signal":""}""")
)
assistant_store_update_state(root, "assistant-core-compat", "running", "resume")
assistant_store_create_child_task(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","objective":"child compatibility","owner_kind":"assistant","resource_policy":"bounded","child_session_id":"assistant-core-child","status":"queued"}""")
)

val session_json = rt_file_read_text("{root}/sessions/assistant-core-compat.json")
val session_value = json_parse(session_json)
match session_value:
    case nil:
        fail("session JSON should parse")
    case _:
        expect(json_to_string(json_object_get(session_value, "id"))).to_equal("assistant-core-compat")
        expect(json_to_string(json_object_get(session_value, "state"))).to_equal("running")
        expect(json_get_type(json_object_get(session_value, "updated_at"))).to_equal("number")
        expect(json_get_type(json_object_get(session_value, "child_tasks"))).to_equal("array")
        expect(json_array_length(json_object_get(session_value, "child_tasks"))).to_equal(1)

val timeline_jsonl = rt_file_read_text("{root}/timelines/assistant-core-compat.jsonl")
expect(non_empty_lines_count(timeline_jsonl)).to_equal(3)  # oracle: 3 — named expected value from the requirement
val first_line = json_parse(timeline_jsonl.split("\n")[0])
match first_line:
    case nil:
        fail("timeline JSONL first line should parse")
    case _:
        expect(json_to_string(json_object_get(first_line, "kind"))).to_equal("note")
```

</details>

#### durably prunes timeline and notification jsonl tails while preserving digest checkpoint

- durably prunes timeline and notification jsonl tails while preserving digest checkpoint
- Verify: durably prunes timeline and notification jsonl tails while preserving digest checkpoint
   - Expected: result.status equals `pruned`
   - Expected: result.reason equals `retention_applied`
   - Expected: result.retained_timeline_count equals `3`
   - Expected: result.retained_notification_count equals `2`
   - Expected: result.dropped_timeline_count equals `4`
   - Expected: result.dropped_notification_count equals `5`
   - Expected: result.digest_checkpoint_id equals `digest-keep`
   - Expected: result.evidence.split("nil").len() equals `1`
   - Expected: non_empty_lines_count(timeline_jsonl) equals `3`
   - Expected: non_empty_lines_count(notifications_jsonl) equals `2`
   - Expected: timeline_jsonl.split("event-0").len() equals `1`
   - Expected: session.event_count equals `3`
   - Expected: session.digest_checkpoint_id equals `digest-keep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("durably prunes timeline and notification jsonl tails while preserving digest checkpoint")
step("Verify: durably prunes timeline and notification jsonl tails while preserving digest checkpoint")
val root = test_root("retention")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-retention-core","name":"Retention Core","summary":"retention","objective":"retention","prompt":"retention","mode":"proactive","state":"running","digest_checkpoint_id":"digest-keep"}""")
)
var i: i64 = 0
while i < 7:
    assistant_store_append_event(
        root,
        json_parse("{\"session_id\":\"assistant-retention-core\",\"kind\":\"note\",\"message\":\"event-{i}\",\"signal\":\"\",\"timestamp_ms\":{i},\"event_id\":\"event-{i}\"}")
    )
    i = i + 1

val result = assistant_store_prune_session_retention(root, "assistant-retention-core", 3, 2)

expect(result.status).to_equal("pruned")
expect(result.reason).to_equal("retention_applied")
expect(result.retained_timeline_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result.retained_notification_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.dropped_timeline_count).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(result.dropped_notification_count).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(result.digest_checkpoint_id).to_equal("digest-keep")
expect(result.evidence.split("nil").len()).to_equal(1)

val timeline_jsonl = rt_file_read_text("{root}/timelines/assistant-retention-core.jsonl")
val notifications_jsonl = rt_file_read_text("{root}/notifications/assistant-retention-core.jsonl")
expect(non_empty_lines_count(timeline_jsonl)).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(non_empty_lines_count(notifications_jsonl)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(timeline_jsonl).to_contain("event-4")
expect(timeline_jsonl).to_contain("event-6")
expect(timeline_jsonl.split("event-0").len()).to_equal(1)

val loaded = assistant_store_load_session(root, "assistant-retention-core")
match loaded:
    case Some(session):
        expect(session.event_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
        expect(session.digest_checkpoint_id).to_equal("digest-keep")
    case nil:
        fail("retained assistant session should load after pruning")
```

</details>

#### generates durable digest checkpoints and prunes old checkpoint entries

- generates durable digest checkpoints and prunes old checkpoint entries
- Verify: generates durable digest checkpoints and prunes old checkpoint entries
   - Expected: first.status equals `generated`
   - Expected: first.reason equals `digest_generated`
   - Expected: first.retained_checkpoint_count equals `1`
   - Expected: first.dropped_checkpoint_count equals `0`
   - Expected: second.status equals `generated`
   - Expected: second.retained_checkpoint_count equals `1`
   - Expected: second.dropped_checkpoint_count equals `1`
   - Expected: second.evidence.split("nil").len() equals `1`
   - Expected: non_empty_lines_count(digest_jsonl) equals `1`
   - Expected: digest_jsonl.split(first.checkpoint_id).len() equals `1`
   - Expected: session.digest_checkpoint_id equals `second.checkpoint_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates durable digest checkpoints and prunes old checkpoint entries")
step("Verify: generates durable digest checkpoints and prunes old checkpoint entries")
val root = test_root("digest")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-digest-core","name":"Digest Core","summary":"digest","objective":"digest","prompt":"digest","mode":"proactive","state":"running"}""")
)
assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-digest-core","kind":"note","message":"first digest event","signal":"","timestamp_ms":1000,"event_id":"digest-event-1"}""")
)
val first = assistant_store_generate_session_digest(root, "assistant-digest-core", 5)
assistant_store_update_state(root, "assistant-digest-core", "running", "resume")
val second = assistant_store_generate_session_digest(root, "assistant-digest-core", 1)

expect(first.status).to_equal("generated")
expect(first.reason).to_equal("digest_generated")
expect(first.retained_checkpoint_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(first.dropped_checkpoint_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(first.digest_text).to_contain("events=1")
expect(second.status).to_equal("generated")
expect(second.retained_checkpoint_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(second.dropped_checkpoint_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(second.digest_text).to_contain("recent=resume")
expect(second.evidence.split("nil").len()).to_equal(1)

val digest_jsonl = rt_file_read_text("{root}/digests/assistant-digest-core.jsonl")
expect(non_empty_lines_count(digest_jsonl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(digest_jsonl).to_contain(second.checkpoint_id)
expect(digest_jsonl.split(first.checkpoint_id).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement

val loaded = assistant_store_load_session(root, "assistant-digest-core")
match loaded:
    case Some(session):
        expect(session.digest_checkpoint_id).to_equal(second.checkpoint_id)
    case nil:
        fail("assistant session should retain generated digest checkpoint id")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-MCP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9121e0e3afeba26f7f8563df5bbdd10bdada9958acb799cdfd43cbbed0de35c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9121e0e3afeba26f7f8563df5bbdd10bdada9958acb799cdfd43cbbed0de35c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9121e0e3afeba26f7f8563df5bbdd10bdada9958acb799cdfd43cbbed0de35c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp/assistant/session_store_spec.spl
mirror: doc/06_spec/unit/app/mcp/assistant/session_store_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp/assistant/session_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp/assistant/session_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp/assistant/session_store_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp/assistant/session_store_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-object root inputs and generates missing session ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/assistant/session_store_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes signal events without hanging and preserves wake reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/assistant/session_store_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates, loads, updates, and tracks child metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
