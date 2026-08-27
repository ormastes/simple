# Claude Full AttachmentMessage Skill Discovery

> Exercises the production `AttachmentMessage.spl` dispatcher for ordered skill

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AttachmentMessage Skill Discovery

Exercises the production `AttachmentMessage.spl` dispatcher for ordered skill

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the production `AttachmentMessage.spl` dispatcher for ordered skill
discovery metadata, demo feedback suppression, and fail-closed hidden states.

REQ-LLM-CARET-HIDDEN-008

Claim boundary: this is supporting parts-bin render-model evidence. It proves
`AttachmentRender` metadata returned by the production dispatcher, not shipped
CLI/TUI reachability, hosted UI behavior, widgets, or pixels.

## Scenarios

### Claude full AttachmentMessage

### REQ-LLM-CARET-HIDDEN-008: supporting skill-discovery render metadata

#### render ordered plural skill discovery through AttachmentMessage

- render ordered plural skill discovery through AttachmentMessage
- Load the skill-discovery attachment fixture
- Render skill discovery through AttachmentMessage
- Check skill-discovery content and redaction
   - Expected: check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3] /skill-feedback sk-1") equals `complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-HIDDEN-008
# @req REQ-SSPEC-SYSTEM
step("render ordered plural skill discovery through AttachmentMessage")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Load the skill-discovery attachment fixture")
val attachment = setup_attachment_skill_discovery_fixture()
step("Render skill discovery through AttachmentMessage")
val render = attachmentMessageRender(attachment, false, false, false, false, true, false)
step("Check skill-discovery content and redaction")
expect(check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3] /skill-feedback sk-1")).to_equal("complete")
```

</details>

#### suppress first-skill feedback in demo without changing ordered content

- suppress first-skill feedback in demo without changing ordered content
- Load the skill-discovery attachment fixture
- Render skill discovery through AttachmentMessage
- Check skill-discovery content and redaction
   - Expected: check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3]") equals `complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suppress first-skill feedback in demo without changing ordered content")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Load the skill-discovery attachment fixture")
val attachment = setup_attachment_skill_discovery_fixture()
step("Render skill discovery through AttachmentMessage")
val render = attachmentMessageRender(attachment, true, true, true, true, true, true)
step("Check skill-discovery content and redaction")
expect(check_attachment_skill_discovery_render(render, "search [sk-1], deploy, review [sk-3]")).to_equal("complete")
```

</details>

#### hide disabled empty and wrong-type skill discovery without leaking content

- hide disabled empty and wrong-type skill discovery without leaking content
- Load the skill-discovery attachment fixture
- Render skill discovery through AttachmentMessage
- Check skill-discovery content and redaction
   - Expected: check_hidden_attachment_render(disabledRender) equals `complete`
   - Expected: check_hidden_attachment_render(emptyRender) equals `complete`
   - Expected: check_hidden_attachment_render(wrongTypeRender) equals `complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hide disabled empty and wrong-type skill discovery without leaking content")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Load the skill-discovery attachment fixture")
val disabledAttachment = setup_attachment_skill_discovery_fixture()
val emptyAttachment = AttachmentModel.empty("skill_discovery")
val wrongTypeAttachment = AttachmentModel.empty("unsupported_skill_discovery")
wrongTypeAttachment.skills = [AttachmentSkill.new("private-skill", "secret-short-id")]
step("Render skill discovery through AttachmentMessage")
val disabledRender = attachmentMessageRender(disabledAttachment, false, false, false, false, false, false)
val emptyRender = attachmentMessageRender(emptyAttachment, false, false, false, false, true, false)
val wrongTypeRender = attachmentMessageRender(wrongTypeAttachment, false, false, false, false, true, false)
step("Check skill-discovery content and redaction")
expect(check_hidden_attachment_render(disabledRender)).to_equal("complete")
expect(check_hidden_attachment_render(emptyRender)).to_equal("complete")
expect(check_hidden_attachment_render(wrongTypeRender)).to_equal("complete")
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

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `76c2b2a66a927f592a85f757d2464dfe93b4b912eb6bc87fe5207078f1546b1d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76c2b2a66a927f592a85f757d2464dfe93b4b912eb6bc87fe5207078f1546b1d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76c2b2a66a927f592a85f757d2464dfe93b4b912eb6bc87fe5207078f1546b1d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/messages/AttachmentMessage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
