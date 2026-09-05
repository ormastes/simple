# primitive_transport_spec

> The primitive transport is the complete canonical adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_transport_spec

The primitive transport is the complete canonical adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The primitive transport is the complete canonical adapter.

## Scenarios

### primitive chat transport

#### binds sends deduplicates reads and advances a truthful local cursor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds sends deduplicates reads and advances a truthful local cursor
   - Expected: created.accepted is true
   - Expected: transport.store.create_room(created.room).ok is true
   - Expected: transport.connect("development") equals `connected:primitive:development`
   - Expected: sent equals `accepted:message-1:1`
   - Expected: replay equals `accepted:message-1:1`
   - Expected: transport.history("development", 0, 10).len() equals `1`
   - Expected: transport.mark_read("development", "message-1") equals `local_cursor:1`
   - Expected: transport.store.cursor("development", "reviewer") equals `1`
   - Expected: transport.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("binds sends deduplicates reads and advances a truthful local cursor")
var transport = PrimitiveChatTransport.memory("workspace-1", "reviewer")
val created = create_room("development", "workspace-1", RoomKind.Channel,
    "development", "", "public", "room", "milestones", "previous:2",
    "human-1", 1)
expect(created.accepted).to_equal(true)
expect(transport.store.create_room(created.room).ok).to_equal(true)
expect(transport.connect("development")).to_equal("connected:primitive:development")

val sent = transport.send("development", primitive_message("message-1", "development"),
    "stable-message-key-1")
expect(sent).to_equal("accepted:message-1:1")
val replay = transport.send("development", primitive_message("message-replay", "development"),
    "stable-message-key-1")
expect(replay).to_equal("accepted:message-1:1")
expect(transport.history("development", 0, 10).len()).to_equal(1)
expect(transport.mark_read("development", "message-1")).to_equal("local_cursor:1")
expect(transport.store.cursor("development", "reviewer")).to_equal(1)
expect(transport.close()).to_equal(true)
```

</details>

<details>
<summary>Advanced: creates an ACL-backed canonical direct room</summary>

#### creates an ACL-backed canonical direct room

- creates an ACL-backed canonical direct room
   - Expected: transport.store.room(room_id).kind equals `RoomKind.Direct`
   - Expected: transport.store.memberships().len() equals `2`
   - Expected: transport.connected(room_id) is true
   - Expected: transport.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates an ACL-backed canonical direct room")
var transport = PrimitiveChatTransport.memory("workspace-1", "human-1")
val opened = transport.open_private("unused", ["human-1", "reviewer"])
expect(opened).to_start_with("primitive_direct_room:dm-")
val room_id = opened.substring("primitive_direct_room:".len())
expect(transport.store.room(room_id).kind).to_equal(RoomKind.Direct)
expect(transport.store.memberships().len()).to_equal(2)
expect(transport.connected(room_id)).to_equal(true)
expect(transport.close()).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-002`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-012`
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `181cfa692db9d155da2f17f6b659882ddb646cc4b740b5363c684a122f0f2e14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `181cfa692db9d155da2f17f6b659882ddb646cc4b740b5363c684a122f0f2e14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `181cfa692db9d155da2f17f6b659882ddb646cc4b740b5363c684a122f0f2e14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/primitive_transport_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 7 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds sends deduplicates reads and advances a truthful local cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an ACL-backed canonical direct room' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
