# tier2_transport_adapter_spec

> Tier-two adapter cores expose native requests without overstating receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tier2_transport_adapter_spec

Tier-two adapter cores expose native requests without overstating receipts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tier-two adapter cores expose native requests without overstating receipts.

## Scenarios

### Google Chat, Discord, and Mattermost adapter contracts

#### builds a Google Chat threaded request and reports native read-state intent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a Google Chat threaded request and reports native read-state intent
   - Expected: chat.bind_space("binding-1", "development", "spaces/AAA") equals `binding_attached`
   - Expected: request.url equals `https://chat.googleapis.com/v1/spaces/AAA/messages`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a Google Chat threaded request and reports native read-state intent")
var chat = GoogleChatTransport.new("google-token")
expect(chat.bind_space("binding-1", "development", "spaces/AAA")).to_equal("binding_attached")
val request = chat.prepare_send("binding-1", tier2_message(), "stable-key-google")
expect(request.url).to_equal("https://chat.googleapis.com/v1/spaces/AAA/messages")
expect(request.body).to_contain("spaces/AAA/threads/thread-1")
expect(chat.mark_read("binding-1", "remote-message-1")).to_start_with(
    "google_chat_native_read_state:")
```

</details>

#### builds a Discord reply request while keeping human read truth local

- builds a Discord reply request while keeping human read truth local
   - Expected: discord.bind_channel("binding-2", "development", "1234") equals `binding_attached`
   - Expected: request.url equals `https://discord.com/api/v10/channels/1234/messages`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a Discord reply request while keeping human read truth local")
var discord = DiscordChatTransport.new("discord-token")
expect(discord.bind_channel("binding-2", "development", "1234")).to_equal("binding_attached")
val request = discord.prepare_send("binding-2", tier2_message(), "stable-key-discord")
expect(request.url).to_equal("https://discord.com/api/v10/channels/1234/messages")
expect(request.body).to_contain("message_reference")
expect(discord.mark_read("binding-2", "remote-message-1")).to_equal(
    "primitive_sidecar:mark_read:remote-message-1")
```

</details>

#### builds a Mattermost root reply and supports native direct-channel intent

- builds a Mattermost root reply and supports native direct-channel intent
   - Expected: mattermost.bind_channel("binding-3", "development", "channel-1") equals `binding_attached`
   - Expected: request.url equals `https://mattermost.example/api/v4/posts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a Mattermost root reply and supports native direct-channel intent")
var mattermost = MattermostChatTransport.new("https://mattermost.example/", "mattermost-token")
expect(mattermost.bind_channel("binding-3", "development", "channel-1")).to_equal("binding_attached")
val request = mattermost.prepare_send("binding-3", tier2_message(), "stable-key-mattermost")
expect(request.url).to_equal("https://mattermost.example/api/v4/posts")
expect(request.body).to_contain("root_id")
expect(mattermost.open_private("binding-3", ["human-1", "agent-1"])).to_equal(
    "mattermost_native_direct_channel:create")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `2d3aa68ade4b75d9ee35e78215474f9ddf3d3ed5c4378aa4e59cf495d54a6aa3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d3aa68ade4b75d9ee35e78215474f9ddf3d3ed5c4378aa4e59cf495d54a6aa3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d3aa68ade4b75d9ee35e78215474f9ddf3d3ed5c4378aa4e59cf495d54a6aa3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a Google Chat threaded request and reports native read-state intent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a Discord reply request while keeping human read truth local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/tier2_transport_adapter_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a Mattermost root reply and supports native direct-channel intent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
