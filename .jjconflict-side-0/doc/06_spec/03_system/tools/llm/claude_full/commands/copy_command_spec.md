# Claude Full Copy Command

> Mirrors `tmp/claude/claude-code-main/src/commands/copy` metadata, assistant

<!-- sdn-diagram:id=copy_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=copy_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

copy_command_spec -> std
copy_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=copy_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Copy Command

Mirrors `tmp/claude/claude-code-main/src/commands/copy` metadata, assistant

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/copy_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/copy` metadata, assistant
message selection, code-block picker decisions, filename sanitization, and
copy/write result text.

## Scenarios

### Claude full copy command

#### matches command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = copyCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("copy")
expect(command.description).to_equal("Copy Claude's last response to clipboard (or /copy N for the Nth-latest)")
expect(command.loadPath).to_equal("./copy.js")
expect(copyIndexSourceLinesModeled()).to_equal(15)
```

</details>

#### collects recent assistant text newest first and skips unusable turns

- CopyMessage assistant
- CopyMessage user
- CopyMessage api error
- CopyMessage assistant
- CopyMessage assistant
   - Expected: texts.len() equals `2`
   - Expected: texts[0] equals `new\n\nanswer`
   - Expected: texts[1] equals `old answer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val messages = [
    CopyMessage.assistant(["old answer"]),
    CopyMessage.user(["question"]),
    CopyMessage.api_error(["bad"]),
    CopyMessage.assistant([""]),
    CopyMessage.assistant(["new", "answer"])
]
val texts = collectRecentAssistantTexts(messages)
expect(texts.len()).to_equal(2)
expect(texts[0]).to_equal("new\n\nanswer")
expect(texts[1]).to_equal("old answer")
```

</details>

#### parses fenced code blocks and picker options

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markdown = "Lead\n```ts\nconst x = 1\n```\nMiddle\n```../../etc/passwd\nsecret\nline2\n```"
val blocks = extractCodeBlocks(markdown)
expect(blocks.len()).to_equal(2)
expect(blocks[0].lang).to_equal("ts")
expect(blocks[0].code).to_equal("const x = 1")
expect(blocks[1].lang).to_equal("../../etc/passwd")
expect(blocks[1].code).to_equal("secret\nline2")
expect(fileExtension(blocks[1].lang)).to_equal(".etcpasswd")
expect(fileExtension("plaintext")).to_equal(".txt")

val options = pickerOptions("full\ntext", blocks)
expect(options.len()).to_equal(4)
expect(options[0].label).to_equal("Full response")
expect(options[0].value).to_equal("full")
expect(options[0].description).to_equal("9 chars, 2 lines")
expect(options[1].label).to_equal("const x = 1")
expect(options[1].description).to_equal("ts")
expect(options[2].description).to_equal("../../etc/passwd, 2 lines")
expect(options[3].label).to_equal("Always copy full response")
expect(truncateLine("abcdefghijklmnopqrstuvwxyz", 10)).to_equal("abcdefg...")
```

</details>

#### selects full text, code blocks, always preference, and write shortcut

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = [CopyCodeBlock.new("print(1)", "python"), CopyCodeBlock.new("{}", "jsonc")]
val full = selectionContent("full text", blocks, "full")
expect(full.text).to_equal("full text")
expect(full.filename).to_equal("response.md")
expect(full.blockIndex).to_equal(-1)

val block = selectionContent("full text", blocks, "1")
expect(block.text).to_equal("{}")
expect(block.filename).to_equal("copy.jsonc")
expect(block.blockIndex).to_equal(1)
expect(handlePickerSelect("full text", blocks, "always", 0, true)).to_contain("Preference saved")
expect(handlePickerSelect("full text", blocks, "0", 0, true)).to_contain("copy.python")
expect(handlePickerWrite("full text", blocks, "0", true, "")).to_equal("Written to /tmp/claude/copy.python")
expect(handlePickerWrite("full text", blocks, "0", false, "disk full")).to_equal("Failed to write file: disk full")
expect(copyCancelledMessage()).to_equal("Copy cancelled")
```

</details>

#### routes command calls for no message, argument errors, copy, and picker

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none = callCopy([CopyMessage.user(["hello"])], "", false, true)
expect(none.doneMessage).to_equal("No assistant message to copy")
expect(none.renderPicker).to_equal(false)

val one = CopyMessage.assistant(["first"])
val two = CopyMessage.assistant(["second"])
val bad = callCopy([one, two], "abc", false, true)
expect(bad.doneMessage).to_contain("Usage: /copy [N]")
val tooFar = callCopy([one], "2", false, true)
expect(tooFar.doneMessage).to_equal("Only 1 assistant message available to copy")

val older = callCopy([one, two], "2", false, true)
expect(older.selectedAge).to_equal(1)
expect(older.selectedText).to_equal("first")
expect(older.doneMessage).to_contain("Copied to clipboard")
expect(older.doneMessage).to_contain("Also written to /tmp/claude/response.md")

val withBlock = callCopy([CopyMessage.assistant(["```sh\necho hi\n```"])], "", false, true)
expect(withBlock.renderPicker).to_equal(true)
expect(withBlock.blockCount).to_equal(1)
val forced = callCopy([CopyMessage.assistant(["```sh\necho hi\n```"])], "", true, false)
expect(forced.renderPicker).to_equal(false)
expect(forced.doneMessage).to_equal(copyOrWriteResult("```sh\necho hi\n```", "response.md", false))
expect(copySourceLinesModeled()).to_equal(370)
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
