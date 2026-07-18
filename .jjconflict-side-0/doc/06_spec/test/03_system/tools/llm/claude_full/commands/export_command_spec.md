# Claude Full Export Command

> Mirrors `tmp/claude/claude-code-main/src/commands/export` metadata, first prompt

<!-- sdn-diagram:id=export_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_command_spec -> std
export_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/export` metadata, first prompt
extraction, filename sanitation, direct write routing, and dialog default names.

## Scenarios

### Claude full export command

#### matches command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- ExportMessage assistant
- ExportMessage user
- ExportMessage user
   - Expected: extractFirstPrompt(messages) equals `First line`
- ExportMessage user parts
   - Expected: extractFirstPrompt(partMessages) equals `Array text`
   - Expected: extractFirstPrompt([ExportMessage.user(longPrompt)]) equals `"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVW…")`
   - Expected: extractFirstPrompt([ExportMessage.assistant("none")]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(finalExportFilename("notes.txt")).to_equal("notes.txt")
expect(finalExportFilename("notes.md")).to_equal("notes.txt")
expect(finalExportFilename("notes")).to_equal("notes.txt")
```

</details>

#### routes direct writes, write failures, and no-arg dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
