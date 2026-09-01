# tier3_transport_adapter_spec

> Tier-three adapters expose only genuine LINE and KakaoTalk API subsets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tier3_transport_adapter_spec

Tier-three adapters expose only genuine LINE and KakaoTalk API subsets.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tier-three adapters expose only genuine LINE and KakaoTalk API subsets.

## Scenarios

### LINE and KakaoTalk limited adapter contracts

#### sends to an existing LINE chat with a supported quote token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sends to an existing LINE chat with a supported quote token
   - Expected: request.url equals `https://api.line.me/v2/bot/message/push`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sends to an existing LINE chat with a supported quote token")
var line = LineChatTransport.new("line-channel-token")
expect(line.bind_existing_chat("line-binding", "development", "line-group-1")).to_equal(
    "binding_attached")
val request = line.prepare_send("line-binding", tier3_message(), "stable-key-line")
expect(request.url).to_equal("https://api.line.me/v2/bot/message/push")
expect(request.body).to_contain("quoteToken")
expect(line.open_private("line-binding", ["human-1", "agent-1"])).to_equal(
    "primitive_sidecar:open_private")
```

</details>

#### limits KakaoTalk to self or authorized-friend message APIs

- limits KakaoTalk to self or authorized-friend message APIs
   - Expected: kakao.bind_self("kakao-self", "development") equals `binding_attached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("limits KakaoTalk to self or authorized-friend message APIs")
var kakao = KakaoChatTransport.new("kakao-user-token")
expect(kakao.bind_self("kakao-self", "development")).to_equal("binding_attached")
val self_request = kakao.prepare_send("kakao-self", tier3_message(), "stable-key-kakao-self")
expect(self_request.url).to_contain("/talk/memo/default/send")
expect(self_request.body).to_start_with("template_object=")
expect(kakao.bind_friend("kakao-friend", "development", "friend-uuid-1")).to_equal(
    "binding_attached")
val friend_request = kakao.prepare_send("kakao-friend", tier3_message(), "stable-key-kakao-friend")
expect(friend_request.url).to_contain("/talk/friends/message/default/send")
expect(friend_request.body).to_contain("receiver_uuids=")
expect(kakao.open_private("kakao-friend", ["human-1", "agent-1"])).to_equal(
    "primitive_sidecar:open_private")
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
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90d2f6e768afb5a4f5135085bd876a3b2b14fdf12537ca8536fa84fd20b4c558`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90d2f6e768afb5a4f5135085bd876a3b2b14fdf12537ca8536fa84fd20b4c558`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90d2f6e768afb5a4f5135085bd876a3b2b14fdf12537ca8536fa84fd20b4c558`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends to an existing LINE chat with a supported quote token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/tier3_transport_adapter_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'limits KakaoTalk to self or authorized-friend message APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
