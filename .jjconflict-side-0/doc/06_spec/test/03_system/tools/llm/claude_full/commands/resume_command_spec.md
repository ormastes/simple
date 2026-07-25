# Claude Full Resume Command

> Mirrors `tmp/claude/claude-code-main/src/commands/resume` for command metadata,

<!-- sdn-diagram:id=resume_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resume_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resume_command_spec -> std
resume_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resume_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Resume Command

Mirrors `tmp/claude/claude-code-main/src/commands/resume` for command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/resume_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/resume` for command metadata,
picker filtering, argument resolution, title search, and picker cross-project
results.

## Scenarios

### Claude full resume command

#### matches command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = resumeCommand()

expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("resume")
expect(command.description).to_equal("Resume a previous conversation")
expect(command.aliases.len()).to_equal(1)
expect(command.aliases[0]).to_equal("continue")
expect(command.argumentHint).to_equal("[conversation id or search term]")
expect(command.loadPath).to_equal("./resume.js")
expect(resumeIndexSourceLinesModeled()).to_equal(12)
```

</details>

#### filters picker sessions and exposes picker states

- ResumeLog new
- ResumeLog new
- ResumeLog new
   - Expected: resumable.len() equals `1`
   - Expected: resumable[0].sessionId equals `keep`
   - Expected: resumeLoadingMessage() equals `Loading conversations...`
   - Expected: resumeResumingMessage() equals `Resuming conversation...`
   - Expected: resumeNoConversationsResult().doneMessage equals `No conversations found to resume`
   - Expected: resumeLoadFailureResult().doneMessage equals `Failed to load conversations`
   - Expected: resumeCancelResult().doneMessage equals `Resume cancelled`
   - Expected: resumeCancelResult().display equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logs = [
    ResumeLog.new("current", false, false, 1, "/repo", ""),
    ResumeLog.new("side", true, false, 2, "/repo", ""),
    ResumeLog.new("keep", false, true, 3, "/repo", ""),
]

val resumable = filterResumableSessions(logs, "current")
expect(resumable.len()).to_equal(1)
expect(resumable[0].sessionId).to_equal("keep")
expect(resumeLoadingMessage()).to_equal("Loading conversations...")
expect(resumeResumingMessage()).to_equal("Resuming conversation...")
expect(resumeNoConversationsResult().doneMessage).to_equal("No conversations found to resume")
expect(resumeLoadFailureResult().doneMessage).to_equal("Failed to load conversations")
expect(resumeCancelResult().doneMessage).to_equal("Resume cancelled")
expect(resumeCancelResult().display).to_equal("system")
```

</details>

#### resolves no-arg picker, UUID logs, and direct fallback logs

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uuid = "12345678-1234-1234-1234-123456789abc"
val older = ResumeLog.new(uuid, false, false, 1, "/repo", "")
val newerLite = ResumeLog.new(uuid, false, true, 5, "/repo", "")
val directUuid = "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa"
val direct = ResumeLog.new(directUuid, false, false, 1, "/repo", "")

val picker = callResume("  ", "current", [older], [], [], false)
expect(picker.renderKind).to_equal("picker")

val byUuid = callResume(uuid, "current", [older, newerLite], [], [], false)
expect(byUuid.renderKind).to_equal("resume")
expect(byUuid.resumedSessionId).to_equal(uuid)
expect(byUuid.entrypoint).to_equal("slash_command_session_id")
expect(byUuid.loadedFullLog).to_equal(true)

val byDirect = callResume(directUuid, "current", [older], [direct], [], false)
expect(byDirect.resumedSessionId).to_equal(directUuid)
expect(byDirect.entrypoint).to_equal("slash_command_session_id")
```

</details>

#### resolves custom titles and errors with Claude help text

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val titled = ResumeLog.new("bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb", false, false, 1, "/repo", "Demo")
val anyLog = ResumeLog.new("cccccccc-cccc-cccc-cccc-cccccccccccc", false, false, 1, "/repo", "")

val byTitle = callResume("Demo", "current", [anyLog], [], [titled], true)
expect(byTitle.resumedSessionId).to_equal("bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb")
expect(byTitle.entrypoint).to_equal("slash_command_title")

val multiple = callResume("Demo", "current", [anyLog], [], [titled, titled], true)
expect(multiple.doneMessage).to_equal("Found 2 sessions matching Demo. Please use /resume to pick a specific session.")

val missing = callResume("missing", "current", [anyLog], [], [], true)
expect(missing.doneMessage).to_equal("Session missing was not found.")
expect(resumeHelpMessage("sessionNotFound", "missing", 0)).to_equal("Session missing was not found.")
expect(resumeErrorPointer("missing")).to_equal("/resume missing")

val empty = callResume("missing", "current", [], [], [], true)
expect(empty.doneMessage).to_equal("No conversations found to resume.")
```

</details>

#### models picker selection, cross-project command output, and failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = ResumeLog.new("dddddddd-dddd-dddd-dddd-dddddddddddd", false, false, 1, "/other", "")

val selected = selectResumeLog(log, false, false, "")
expect(selected.resumedSessionId).to_equal("dddddddd-dddd-dddd-dddd-dddddddddddd")
expect(selected.entrypoint).to_equal("slash_command_picker")

val sameRepoWorktree = selectResumeLog(log, true, true, "")
expect(sameRepoWorktree.entrypoint).to_equal("slash_command_picker")

val crossProject = selectResumeLog(log, true, false, "claude --resume dddddddd-dddd-dddd-dddd-dddddddddddd")
expect(crossProject.display).to_equal("user")
expect(crossProject.doneMessage).to_contain("This conversation is from a different directory.")
expect(crossProject.doneMessage).to_contain("claude --resume dddddddd-dddd-dddd-dddd-dddddddddddd")
expect(crossProject.doneMessage).to_contain("(Command copied to clipboard)")

val invalid = selectResumeLog(ResumeLog.new("not-a-uuid", false, false, 1, "/repo", ""), false, false, "")
expect(invalid.doneMessage).to_equal("Failed to resume conversation")
expect(resumeFailureResult("boom").doneMessage).to_equal("Failed to resume: boom")
expect(validateUuid("not-a-uuid")).to_equal("")
expect(resumeSourceLinesModeled()).to_equal(274)
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
