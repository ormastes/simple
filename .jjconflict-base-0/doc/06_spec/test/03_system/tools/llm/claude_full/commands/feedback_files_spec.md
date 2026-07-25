# Claude Full Feedback and Files Commands

> Checks modern SSpec parity for feedback and files command descriptors.

<!-- sdn-diagram:id=feedback_files_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feedback_files_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feedback_files_spec -> std
feedback_files_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feedback_files_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Feedback and Files Commands

Checks modern SSpec parity for feedback and files command descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/feedback_files_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for feedback and files command descriptors.

## Scenarios

### Claude full feedback files commands

#### should expose feedback command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(feedbackCommandName()).to_equal("feedback")
expect(feedbackCommandDescription()).to_contain("feedback")
expect(feedbackCommandUrl()).to_contain("github.com")
expect(feedbackCommandMessage()).to_contain("Opening feedback")
```

</details>

#### should expose files command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(filesCommandName()).to_equal("files")
expect(filesCommand().description).to_contain("current conversation")
expect(filesCommand().typeName).to_equal("local-jsx")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(feedbackCommandSourceLinesModeled()).to_equal(24)
expect(feedbackIndexSourceLinesModeled()).to_equal(26)
expect(filesCommandSourceLinesModeled()).to_equal(19)
expect(filesIndexSourceLinesModeled()).to_equal(12)
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
