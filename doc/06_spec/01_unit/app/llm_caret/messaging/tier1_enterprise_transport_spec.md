# tier1_enterprise_transport_spec

> Teams and Telegram adapters preserve genuine platform constraints.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tier1_enterprise_transport_spec

Teams and Telegram adapters preserve genuine platform constraints.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Teams and Telegram adapters preserve genuine platform constraints.

## Scenarios

### Teams and Telegram adapter contracts

#### constructs a Teams proactive reply only for a bound conversation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a Teams proactive reply only for a bound conversation
   - Expected: teams.connect("binding-1") equals `connected:teams:binding-1`
   - Expected: request.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("constructs a Teams proactive reply only for a bound conversation")
var teams = TeamsChatTransport.new("teams-bearer")
expect(teams.bind_conversation("binding-1", "development",
    "https://smba.trafficmanager.net/emea", "conversation-1")).to_equal("binding_attached")
expect(teams.connect("binding-1")).to_equal("connected:teams:binding-1")
val request = teams.prepare_send("binding-1", platform_message("", ""), "stable-key-3")
expect(request.accepted).to_equal(true)
expect(request.url).to_equal(
    "https://smba.trafficmanager.net/emea/v3/conversations/conversation-1/activities/activity-root")
expect(request.body).to_contain("clientActivityId")
expect(teams.mark_read("binding-1", "activity-1")).to_equal(
    "primitive_sidecar:mark_read:activity-1")
expect(teams.open_private("binding-1", ["human-1", "agent-1"])).to_equal(
    "teams_existing_installation_required:proactive_conversation")
```

</details>

#### uses Telegram native replies only with a mapped external message ID

- uses Telegram native replies only with a mapped external message ID
   - Expected: telegram.bind_chat("binding-1", "development", "-100123") equals `binding_attached`
   - Expected: telegram.connect("binding-1") equals `connected:telegram:binding-1`
   - Expected: fallback.body does not contain `reply_parameters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses Telegram native replies only with a mapped external message ID")
var telegram = TelegramChatTransport.new("telegram-test-token")
expect(telegram.bind_chat("binding-1", "development", "-100123")).to_equal("binding_attached")
expect(telegram.connect("binding-1")).to_equal("connected:telegram:binding-1")
val native_reply = telegram.prepare_send("binding-1", platform_message("canonical-4", "42"),
    "stable-key-4")
expect(native_reply.url).to_contain("/sendMessage")
expect(native_reply.body).to_contain("\"reply_parameters\":{\"message_id\":42}")
val fallback = telegram.prepare_send("binding-1", platform_message("canonical-4", ""),
    "stable-key-5")
expect(fallback.body).to_contain("reply to #canonical-4")
expect(fallback.body.contains("reply_parameters")).to_equal(false)
expect(telegram.open_private("binding-1", ["human-1", "agent-1"])).to_equal(
    "telegram_existing_chat_required")
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

- Canonical SPipe generation for source `778cdfed1134f69c5890fc1326d807a27ac62910e6f2a33744b368f52a97e5c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `778cdfed1134f69c5890fc1326d807a27ac62910e6f2a33744b368f52a97e5c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `778cdfed1134f69c5890fc1326d807a27ac62910e6f2a33744b368f52a97e5c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a Teams proactive reply only for a bound conversation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses Telegram native replies only with a mapped external message ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
