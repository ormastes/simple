# Claude Full Agent File Utils

> Checks agent metadata filename derivation, safe paths, parsing, formatting,

<!-- sdn-diagram:id=agent_file_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_file_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_file_utils_spec -> std
agent_file_utils_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_file_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent File Utils

Checks agent metadata filename derivation, safe paths, parsing, formatting,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_file_utils_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks agent metadata filename derivation, safe paths, parsing, formatting,
empty/error behavior, and source parity helpers.

## Scenarios

### Claude full agentFileUtils

#### validates names, models, filenames, and safe paths

- Validate accepted and rejected names
   - Expected: isValidAgentName("review-bot") is true
   - Expected: isValidAgentName("Review Bot") is false
   - Expected: isValidAgentName("../review") is false
   - Expected: isValidAgentModel("claude-sonnet-4") is true
   - Expected: isValidAgentModel("../model") is false
- Derive slugs and metadata paths
   - Expected: slugifyAgentName("Review Bot_v2") equals `review-bot-v2`
   - Expected: deriveAgentMetadataFilename("Review Bot_v2") equals `review-bot-v2.md`
   - Expected: agentMetadataPath("/repo/.claude/agents/", "Review Bot") equals `/repo/.claude/agents/review-bot.md`
- Reject traversal and non-markdown paths
   - Expected: isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/review-bot.md") is true
   - Expected: isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/../secrets.md") is false
   - Expected: isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/review-bot.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate accepted and rejected names")
expect(isValidAgentName("review-bot")).to_equal(true)
expect(isValidAgentName("Review Bot")).to_equal(false)
expect(isValidAgentName("../review")).to_equal(false)
expect(isValidAgentModel("claude-sonnet-4")).to_equal(true)
expect(isValidAgentModel("../model")).to_equal(false)

step("Derive slugs and metadata paths")
expect(slugifyAgentName("Review Bot_v2")).to_equal("review-bot-v2")
expect(deriveAgentMetadataFilename("Review Bot_v2")).to_equal("review-bot-v2.md")
expect(agentMetadataPath("/repo/.claude/agents/", "Review Bot")).to_equal("/repo/.claude/agents/review-bot.md")

step("Reject traversal and non-markdown paths")
expect(isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/review-bot.md")).to_equal(true)
expect(isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/../secrets.md")).to_equal(false)
expect(isSafeAgentFilePath("/repo/.claude/agents", "/repo/.claude/agents/review-bot.txt")).to_equal(false)
```

</details>

#### parses and formats agent markdown

- Parse frontmatter and body
   - Expected: parsed.ok is true
   - Expected: parsed.metadata.name equals `review-bot`
   - Expected: parsed.metadata.description equals `Reviews changes`
   - Expected: parsed.metadata.model equals `claude-sonnet-4`
   - Expected: parsed.body equals `Use concise review notes.`
- Format metadata back to markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse frontmatter and body")
val parsed = parseAgentFile("/repo/.claude/agents/review-bot.md", "---\nname: review-bot\ndescription: Reviews changes\nmodel: claude-sonnet-4\n---\nUse concise review notes.\n")
expect(parsed.ok).to_equal(true)
expect(parsed.metadata.name).to_equal("review-bot")
expect(parsed.metadata.description).to_equal("Reviews changes")
expect(parsed.metadata.model).to_equal("claude-sonnet-4")
expect(parsed.body).to_equal("Use concise review notes.")

step("Format metadata back to markdown")
val formatted = formatAgentFile(parsed.metadata, parsed.body)
expect(formatted).to_contain("name: review-bot")
expect(formatted).to_contain("description: Reviews changes")
expect(formatted).to_contain("model: claude-sonnet-4")
expect(formatted).to_end_with("Use concise review notes.\n")
```

</details>

#### returns errors for empty and malformed files

- Reject empty content
   - Expected: empty.ok is false
   - Expected: empty.error equals `agent file is empty`
- Reject unclosed frontmatter
   - Expected: malformed.ok is false
   - Expected: malformed.error equals `frontmatter is not closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject empty content")
val empty = parseAgentFile("/repo/.claude/agents/review-bot.md", "")
expect(empty.ok).to_equal(false)
expect(empty.error).to_equal("agent file is empty")

step("Reject unclosed frontmatter")
val malformed = parseAgentFile("/repo/.claude/agents/review-bot.md", "---\nname: review-bot\n")
expect(malformed.ok).to_equal(false)
expect(malformed.error).to_equal("frontmatter is not closed")
```

</details>

#### exports source parity helpers

- Check source helper output
   - Expected: agentFileSourceHelper("Review Bot") equals `agentFileUtils:review-bot.md`
   - Expected: agentFileUtilsSourceHelpersModeled() equals `validation,slug,filename,path,parse,format,source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check source helper output")
expect(agentFileSourceHelper("Review Bot")).to_equal("agentFileUtils:review-bot.md")
expect(agentFileUtilsSourceHelpersModeled()).to_equal("validation,slug,filename,path,parse,format,source")
expect(agentFileUtilsSourceLinesModeled()).to_be_greater_than(271)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
