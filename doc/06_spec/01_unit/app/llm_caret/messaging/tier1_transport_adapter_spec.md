# tier1_transport_adapter_spec

> Tier-one adapter cores preserve canonical IDs, threads, and capability truth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tier1_transport_adapter_spec

Tier-one adapter cores preserve canonical IDs, threads, and capability truth.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tier-one adapter cores preserve canonical IDs, threads, and capability truth.

## Scenarios

### Matrix and Slack adapter contracts

<details>
<summary>Advanced: constructs a native Matrix threaded send and deduplicates inbound events</summary>

#### constructs a native Matrix threaded send and deduplicates inbound events

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a native Matrix threaded send and deduplicates inbound events
   - Expected: matrix.bind_room("binding-1", "development", "!room:example") equals `binding_attached`
   - Expected: matrix.connect("binding-1") equals `connected:matrix:binding-1`
   - Expected: request.accepted is true
   - Expected: request.method equals `PUT`
   - Expected: first.canonical_room_id equals `development`
   - Expected: first.thread_root_id equals `remote-thread-1`
   - Expected: replay.duplicate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("constructs a native Matrix threaded send and deduplicates inbound events")
var matrix = MatrixChatTransport.new("https://matrix.example", "matrix-token")
expect(matrix.bind_room("binding-1", "development", "!room:example")).to_equal("binding_attached")
expect(matrix.connect("binding-1")).to_equal("connected:matrix:binding-1")
val request = matrix.prepare_send("binding-1", tier1_message(), "stable-key-1")
expect(request.accepted).to_equal(true)
expect(request.method).to_equal("PUT")
expect(request.url).to_contain("/_matrix/client/v3/rooms/%21room%3Aexample/send/m.room.message/")
expect(request.body).to_contain("m.thread")
expect(request.body).to_contain("done \\\"safely\\\"")
val first = matrix.normalize_event("binding-1", inbound_event())
val replay = matrix.normalize_event("binding-1", inbound_event())
expect(first.canonical_room_id).to_equal("development")
expect(first.thread_root_id).to_equal("remote-thread-1")
expect(replay.duplicate).to_equal(true)
expect(matrix.mark_read("binding-1", "remote-message-1")).to_start_with("matrix_native_read_receipt:")
```

</details>


</details>

#### constructs a native Slack threaded send while retaining local read truth

- constructs a native Slack threaded send while retaining local read truth
   - Expected: slack.bind_room("binding-1", "development", "C123") equals `binding_attached`
   - Expected: slack.connect("binding-1") equals `connected:slack:binding-1`
   - Expected: request.accepted is true
   - Expected: request.url equals `https://slack.com/api/chat.postMessage`
   - Expected: normalized.canonical_room_id equals `development`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("constructs a native Slack threaded send while retaining local read truth")
var slack = SlackChatTransport.new("xoxb-test-token")
expect(slack.bind_room("binding-1", "development", "C123")).to_equal("binding_attached")
expect(slack.connect("binding-1")).to_equal("connected:slack:binding-1")
val request = slack.prepare_send("binding-1", tier1_message(), "stable-key-2")
expect(request.accepted).to_equal(true)
expect(request.url).to_equal("https://slack.com/api/chat.postMessage")
expect(request.body).to_contain("\"channel\":\"C123\"")
expect(request.body).to_contain("\"thread_ts\":\"external-thread-1\"")
val normalized = slack.normalize_event("binding-1", inbound_event())
expect(normalized.canonical_room_id).to_equal("development")
expect(slack.mark_read("binding-1", "remote-message-1")).to_equal(
    "primitive_sidecar:mark_read:remote-message-1")
expect(slack.open_private("binding-1", ["human-1", "agent-1"])).to_equal(
    "slack_native_dm:conversations.open")
```

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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d9ad070fabbe0a965890819744d1bb73360d7ae7ef360840f21b2b0827653576`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d9ad070fabbe0a965890819744d1bb73360d7ae7ef360840f21b2b0827653576`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d9ad070fabbe0a965890819744d1bb73360d7ae7ef360840f21b2b0827653576`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a native Matrix threaded send and deduplicates inbound events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/tier1_transport_adapter_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a native Slack threaded send while retaining local read truth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
