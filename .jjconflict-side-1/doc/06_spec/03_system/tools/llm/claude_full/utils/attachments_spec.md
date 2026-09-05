# Claude Full Utils Attachments Slice

> Focused coverage for visible and hidden attachment routing from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Utils Attachments Slice

Focused coverage for visible and hidden attachment routing from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/attachments_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for visible and hidden attachment routing from
`utils/attachments.ts`.

## Scenarios

### Claude full utils attachments parity

#### should model prompt file image command and agent attachment routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model prompt file image command and agent attachment routes
- Check visible attachment routes
   - Expected: file.path equals `README.md`
   - Expected: attachment.visible is true
   - Expected: getAttachmentsRoute(true, true, true) equals `prompt file and context attachments`
   - Expected: getAttachmentsRoute(true, false, true) equals `context attachments`
   - Expected: getAttachmentsRoute(true, false, false) equals `no attachments`
   - Expected: getQueuedCommandAttachmentsRoute(true, true) equals `queued command with output attachments`
   - Expected: getAgentPendingMessageAttachmentsRoute(true, true) equals `agent pending message attachments`
   - Expected: getAgentPendingMessageAttachmentsRoute(true, false) equals `no agent pending attachments`
   - Expected: buildImageContentBlocksRoute(2, true) equals `image content blocks`
   - Expected: buildImageContentBlocksRoute(1, false) equals `invalid image skipped`
   - Expected: modeAttachmentRoute("plan", 2, false) equals `plan mode reminder attachment`
   - Expected: modeAttachmentRoute("auto", 0, true) equals `auto mode exit attachment`
   - Expected: modeAttachmentRoute("auto", 0, false) equals `no mode attachment`
   - Expected: deltaAttachmentRoute("deferred tools", 2) equals `deferred tools delta attachment`
   - Expected: ideAttachmentRoute(true, false) equals `selected ide lines attachment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model prompt file image command and agent attachment routes")
step("Check visible attachment routes")
val file = FileAttachment.new("README.md", "file")
expect(file.path).to_equal("README.md")
val attachment = Attachment.new("file", true)
expect(attachment.visible).to_equal(true)
expect(getAttachmentsRoute(true, true, true)).to_equal("prompt file and context attachments")
expect(getAttachmentsRoute(true, false, true)).to_equal("context attachments")
expect(getAttachmentsRoute(true, false, false)).to_equal("no attachments")
expect(getQueuedCommandAttachmentsRoute(true, true)).to_equal("queued command with output attachments")
expect(getAgentPendingMessageAttachmentsRoute(true, true)).to_equal("agent pending message attachments")
expect(getAgentPendingMessageAttachmentsRoute(true, false)).to_equal("no agent pending attachments")
expect(buildImageContentBlocksRoute(2, true)).to_equal("image content blocks")
expect(buildImageContentBlocksRoute(1, false)).to_equal("invalid image skipped")
expect(modeAttachmentRoute("plan", 2, false)).to_equal("plan mode reminder attachment")
expect(modeAttachmentRoute("auto", 0, true)).to_equal("auto mode exit attachment")
expect(modeAttachmentRoute("auto", 0, false)).to_equal("no mode attachment")
expect(deltaAttachmentRoute("deferred tools", 2)).to_equal("deferred tools delta attachment")
expect(ideAttachmentRoute(true, false)).to_equal("selected ide lines attachment")
```

</details>

#### should model mentions memory skills diagnostics and file attachments

- should model mentions memory skills diagnostics and file attachments
- Check hidden context attachment routes
   - Expected: atMentionRoute("file", true, false) equals `file mention attachment`
   - Expected: atMentionRoute("agent", true, false) equals `agent mention attachment`
   - Expected: atMentionRoute("mcp", true, false) equals `mcp resource attachment`
   - Expected: atMentionRoute("file", true, true) equals `file read denied attachment`
   - Expected: extractMentionRoute("file", true, false, false) equals `quoted file mention`
   - Expected: extractMentionRoute("file", false, true, false) equals `dedupe mention`
   - Expected: extractMentionRoute("file", false, false, true) equals `invalid mention ignored`
   - Expected: extractMentionRoute("mcp", false, false, false) equals `mcp server uri mention`
   - Expected: extractMentionRoute("agent", true, false, false) equals `quoted agent mention`
   - Expected: memoryAttachmentRoute(true, false, false) equals `nested memory attachments`
   - Expected: memoryAttachmentRoute(false, true, true) equals `duplicate memory filtered`
   - Expected: skillAttachmentRoute(true, false, false) equals `dynamic skill attachments`
   - Expected: skillAttachmentRoute(false, true, true) equals `skill listing suppressed`
   - Expected: diagnosticAttachmentRoute(true, true) equals `lsp diagnostic attachments`
   - Expected: diagnosticAttachmentRoute(false, true) equals `diagnostic attachments`
   - Expected: diagnosticAvailabilityRoute(false, true) equals `skip diagnostics without bash tool`
   - Expected: diagnosticAvailabilityRoute(true, true) equals `diagnostics available`
   - Expected: fileAttachmentRoute("file", true, false, false) equals `truncated file attachment`
   - Expected: fileAttachmentRoute("file", false, true, false) equals `pdf reference attachment`
   - Expected: fileAttachmentRoute("file", false, false, true) equals `file read denied attachment`
   - Expected: fileAttachmentRoute("compact", false, false, false) equals `compact file reference attachment`
   - Expected: fileAttachmentRoute("alreadyRead", false, false, false) equals `already read file attachment`
   - Expected: fileReadRoute(true, false, true) equals `already read file attachment`
   - Expected: fileReadRoute(false, true, true) equals `truncated file attachment`
   - Expected: fileReadRoute(false, false, false) equals `file validation error attachment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model mentions memory skills diagnostics and file attachments")
step("Check hidden context attachment routes")
expect(atMentionRoute("file", true, false)).to_equal("file mention attachment")
expect(atMentionRoute("agent", true, false)).to_equal("agent mention attachment")
expect(atMentionRoute("mcp", true, false)).to_equal("mcp resource attachment")
expect(atMentionRoute("file", true, true)).to_equal("file read denied attachment")
expect(extractMentionRoute("file", true, false, false)).to_equal("quoted file mention")
expect(extractMentionRoute("file", false, true, false)).to_equal("dedupe mention")
expect(extractMentionRoute("file", false, false, true)).to_equal("invalid mention ignored")
expect(extractMentionRoute("mcp", false, false, false)).to_equal("mcp server uri mention")
expect(extractMentionRoute("agent", true, false, false)).to_equal("quoted agent mention")
expect(memoryAttachmentRoute(true, false, false)).to_equal("nested memory attachments")
expect(memoryAttachmentRoute(false, true, true)).to_equal("duplicate memory filtered")
expect(skillAttachmentRoute(true, false, false)).to_equal("dynamic skill attachments")
expect(skillAttachmentRoute(false, true, true)).to_equal("skill listing suppressed")
expect(diagnosticAttachmentRoute(true, true)).to_equal("lsp diagnostic attachments")
expect(diagnosticAttachmentRoute(false, true)).to_equal("diagnostic attachments")
expect(diagnosticAvailabilityRoute(false, true)).to_equal("skip diagnostics without bash tool")
expect(diagnosticAvailabilityRoute(true, true)).to_equal("diagnostics available")
expect(fileAttachmentRoute("file", true, false, false)).to_equal("truncated file attachment")
expect(fileAttachmentRoute("file", false, true, false)).to_equal("pdf reference attachment")
expect(fileAttachmentRoute("file", false, false, true)).to_equal("file read denied attachment")
expect(fileAttachmentRoute("compact", false, false, false)).to_equal("compact file reference attachment")
expect(fileAttachmentRoute("alreadyRead", false, false, false)).to_equal("already read file attachment")
expect(fileReadRoute(true, false, true)).to_equal("already read file attachment")
expect(fileReadRoute(false, true, true)).to_equal("truncated file attachment")
expect(fileReadRoute(false, false, false)).to_equal("file validation error attachment")
```

</details>

#### should model reminders team usage context and source floor

- should model reminders team usage context and source floor
- Check reminder and usage routes
   - Expected: reminderAttachmentRoute("todo", true) equals `todo reminder attachment`
   - Expected: reminderAttachmentRoute("task", false) equals `no task reminder`
   - Expected: reminderAvailabilityRoute("todo", false, false, true) equals `skip todo reminder unavailable tool`
   - Expected: reminderAvailabilityRoute("task", true, true, true) equals `skip task reminder in brief`
   - Expected: teamAttachmentRoute(true, false, false) equals `teammate mailbox attachments`
   - Expected: teamAttachmentRoute(false, true, false) equals `team context attachment`
   - Expected: teamAttachmentRoute(false, false, true) equals `pending teammate ids`
   - Expected: teammateMailboxRoute(true, false) equals `teammate mailbox attachments`
   - Expected: teammateMailboxRoute(false, true) equals `pending teammate mailbox ids`
   - Expected: usageAttachmentRoute("token usage", true) equals `token usage attachment`
   - Expected: usageAttachmentRoute("budget", false) equals `no budget attachment`
   - Expected: contextEfficiencyAttachmentRoute(true, false) equals `context efficiency attachment`
   - Expected: contextEfficiencyAttachmentRoute(false, true) equals `compaction reminder attachment`
   - Expected: contextEfficiencyAttachmentRoute(false, false) equals `no context efficiency attachment`
   - Expected: isFileReadDeniedRoute("permission") is true
   - Expected: isFileReadDeniedRoute("other") is false
   - Expected: attachmentsSourceLinesModeled() equals `3997`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model reminders team usage context and source floor")
step("Check reminder and usage routes")
expect(reminderAttachmentRoute("todo", true)).to_equal("todo reminder attachment")
expect(reminderAttachmentRoute("task", false)).to_equal("no task reminder")
expect(reminderAvailabilityRoute("todo", false, false, true)).to_equal("skip todo reminder unavailable tool")
expect(reminderAvailabilityRoute("task", true, true, true)).to_equal("skip task reminder in brief")
expect(teamAttachmentRoute(true, false, false)).to_equal("teammate mailbox attachments")
expect(teamAttachmentRoute(false, true, false)).to_equal("team context attachment")
expect(teamAttachmentRoute(false, false, true)).to_equal("pending teammate ids")
expect(teammateMailboxRoute(true, false)).to_equal("teammate mailbox attachments")
expect(teammateMailboxRoute(false, true)).to_equal("pending teammate mailbox ids")
expect(usageAttachmentRoute("token usage", true)).to_equal("token usage attachment")
expect(usageAttachmentRoute("budget", false)).to_equal("no budget attachment")
expect(contextEfficiencyAttachmentRoute(true, false)).to_equal("context efficiency attachment")
expect(contextEfficiencyAttachmentRoute(false, true)).to_equal("compaction reminder attachment")
expect(contextEfficiencyAttachmentRoute(false, false)).to_equal("no context efficiency attachment")
expect(isFileReadDeniedRoute("permission")).to_equal(true)
expect(isFileReadDeniedRoute("other")).to_equal(false)
expect(attachmentsSourceLinesModeled()).to_equal(3997)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06f80a1a1f1fdcd3a085e43d8f794399546623ecf43ef6574c2e7d8661392d34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06f80a1a1f1fdcd3a085e43d8f794399546623ecf43ef6574c2e7d8661392d34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06f80a1a1f1fdcd3a085e43d8f794399546623ecf43ef6574c2e7d8661392d34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/attachments_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/attachments_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/attachments_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/attachments_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model prompt file image command and agent attachment routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model prompt file image command and agent attachment routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model mentions memory skills diagnostics and file attachments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model mentions memory skills diagnostics and file attachments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model reminders team usage context and source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/attachments_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model reminders team usage context and source floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
