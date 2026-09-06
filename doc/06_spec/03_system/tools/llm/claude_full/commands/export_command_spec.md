# Claude Full Export Command

> Mirrors `tmp/claude/claude-code-main/src/commands/export` metadata, first prompt

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Export Command

Mirrors `tmp/claude/claude-code-main/src/commands/export` metadata, first prompt

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/export_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/export` metadata, first prompt
extraction, filename sanitation, direct write routing, and dialog default names.

## Scenarios

### Claude full export command

#### matches command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches command metadata
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `export`
   - Expected: command.description equals `Export the current conversation to a file or clipboard`
   - Expected: command.argumentHint equals `[filename]`
   - Expected: command.loadPath equals `./export.js`
   - Expected: exportIndexSourceLinesModeled() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches command metadata")
val command = exportCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("export")
expect(command.description).to_equal("Export the current conversation to a file or clipboard")
expect(command.argumentHint).to_equal("[filename]")
expect(command.loadPath).to_equal("./export.js")
expect(exportIndexSourceLinesModeled()).to_equal(11)
```

</details>

#### extracts first user prompt from strings and text parts

- extracts first user prompt from strings and text parts
   - Expected: extractFirstPrompt(messages) equals `First line`
   - Expected: extractFirstPrompt(partMessages) equals `Array text`
   - Expected: extractFirstPrompt([ExportMessage.user(longPrompt)]) equals `abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVW…`
   - Expected: extractFirstPrompt([ExportMessage.assistant("none")]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts first user prompt from strings and text parts")
val messages = [
    ExportMessage.assistant("hello"),
    ExportMessage.user("  First line\nsecond line  "),
    ExportMessage.user("ignored")
]
expect(extractFirstPrompt(messages)).to_equal("First line")

val partMessages = [
    ExportMessage.user_parts([ExportContentPart.image_part(), ExportContentPart.text_part("  Array text\nlater  ")])
]
expect(extractFirstPrompt(partMessages)).to_equal("Array text")

val longPrompt = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
expect(extractFirstPrompt([ExportMessage.user(longPrompt)])).to_equal("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVW…")
expect(extractFirstPrompt([ExportMessage.assistant("none")])).to_equal("")
```

</details>

#### formats timestamps and sanitizes default filenames

- formats timestamps and sanitizes default filenames
   - Expected: timestamp equals `2026-07-05-040302`
   - Expected: sanitizeFilename(" Hello, Claude!!!  Export -- Now ") equals `hello-claude-export-now`
   - Expected: sanitizeFilename("!!!") equals ``
   - Expected: defaultExportFilename([ExportMessage.user(" Hello, Claude!!! ")], timestamp) equals `2026-07-05-040302-hello-claude.txt`
   - Expected: defaultExportFilename([ExportMessage.user("!!!")], timestamp) equals `conversation-2026-07-05-040302.txt`
   - Expected: defaultExportFilename([ExportMessage.assistant("none")], timestamp) equals `conversation-2026-07-05-040302.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats timestamps and sanitizes default filenames")
val timestamp = formatTimestamp(2026, 7, 5, 4, 3, 2)
expect(timestamp).to_equal("2026-07-05-040302")
expect(sanitizeFilename(" Hello, Claude!!!  Export -- Now ")).to_equal("hello-claude-export-now")
expect(sanitizeFilename("!!!")).to_equal("")
expect(defaultExportFilename([ExportMessage.user(" Hello, Claude!!! ")], timestamp)).to_equal("2026-07-05-040302-hello-claude.txt")
expect(defaultExportFilename([ExportMessage.user("!!!")], timestamp)).to_equal("conversation-2026-07-05-040302.txt")
expect(defaultExportFilename([ExportMessage.assistant("none")], timestamp)).to_equal("conversation-2026-07-05-040302.txt")
```

</details>

#### normalizes explicit export filenames

- normalizes explicit export filenames
   - Expected: finalExportFilename("notes.txt") equals `notes.txt`
   - Expected: finalExportFilename("notes.md") equals `notes.txt`
   - Expected: finalExportFilename("notes") equals `notes.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes explicit export filenames")
expect(finalExportFilename("notes.txt")).to_equal("notes.txt")
expect(finalExportFilename("notes.md")).to_equal("notes.txt")
expect(finalExportFilename("notes")).to_equal("notes.txt")
```

</details>

#### routes direct writes, write failures, and no-arg dialog

- routes direct writes, write failures, and no-arg dialog
   - Expected: direct.renderDialog is false
   - Expected: direct.finalFilename equals `session.txt`
   - Expected: direct.filepath equals `/work/session.txt`
   - Expected: direct.doneMessage equals `Conversation exported to: /work/session.txt`
   - Expected: failed.doneMessage equals `Failed to export conversation: disk full`
   - Expected: unknown.doneMessage equals `Failed to export conversation: Unknown error`
   - Expected: dialog.renderDialog is true
   - Expected: dialog.defaultFilename equals `2026-07-05-040302-write-a-test.txt`
   - Expected: dialog.doneMessage equals ``
   - Expected: exportSourceLinesModeled() equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes direct writes, write failures, and no-arg dialog")
val messages = [ExportMessage.user("Write a test"), ExportMessage.assistant("Done")]
val direct = callExport(messages, ["Read"], "session.md", "/work", "2026-07-05-040302", true, "")
expect(direct.renderDialog).to_equal(false)
expect(direct.finalFilename).to_equal("session.txt")
expect(direct.filepath).to_equal("/work/session.txt")
expect(direct.doneMessage).to_equal("Conversation exported to: /work/session.txt")
expect(direct.content).to_contain("user: Write a test")
expect(direct.content).to_contain("Tools: Read")

val failed = callExport(messages, [], "session", "/work", "2026-07-05-040302", false, "disk full")
expect(failed.doneMessage).to_equal("Failed to export conversation: disk full")
val unknown = callExport(messages, [], "session", "/work", "2026-07-05-040302", false, "")
expect(unknown.doneMessage).to_equal("Failed to export conversation: Unknown error")

val dialog = callExport(messages, [], "", "/work", "2026-07-05-040302", true, "")
expect(dialog.renderDialog).to_equal(true)
expect(dialog.defaultFilename).to_equal("2026-07-05-040302-write-a-test.txt")
expect(dialog.doneMessage).to_equal("")
expect(exportSourceLinesModeled()).to_equal(90)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `854c3d00b62611c22f59acd9b6fc407128c4be7fb3a2b3444b2bb48c86b1e21d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `854c3d00b62611c22f59acd9b6fc407128c4be7fb3a2b3444b2bb48c86b1e21d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `854c3d00b62611c22f59acd9b6fc407128c4be7fb3a2b3444b2bb48c86b1e21d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/commands/export_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/export_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/export_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/export_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/export_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/export_command_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/export_command_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts first user prompt from strings and text parts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/export_command_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats timestamps and sanitizes default filenames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
