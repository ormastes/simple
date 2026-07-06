# Claude Full Tag, Theme, Tasks, Stickers, and Thinkback Commands

> Checks modern SSpec parity for a batch of Claude command surfaces.

<!-- sdn-diagram:id=tag_theme_tasks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tag_theme_tasks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tag_theme_tasks_spec -> std
tag_theme_tasks_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tag_theme_tasks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Tag, Theme, Tasks, Stickers, and Thinkback Commands

Checks modern SSpec parity for a batch of Claude command surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/tag_theme_tasks_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for a batch of Claude command surfaces.

## Scenarios

### Claude full tag theme tasks commands

#### should expose command names and summaries

- Read command index names
   - Expected: stickersCommandName() equals `stickers`
   - Expected: tagIndexName() equals `tag`
   - Expected: tasksIndexName() equals `tasks`
   - Expected: themeIndexName() equals `theme`
   - Expected: thinkbackIndexName() equals `thinkback`
- Read visible command summaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read command index names")
expect(stickersCommandName()).to_equal("stickers")
expect(tagIndexName()).to_equal("tag")
expect(tasksIndexName()).to_equal("tasks")
expect(themeIndexName()).to_equal("theme")
expect(thinkbackIndexName()).to_equal("thinkback")

step("Read visible command summaries")
expect(stickerPickerTitle()).to_contain("sticker")
expect(tasksIndexDescription()).to_contain("tasks")
expect(themeIndexDescription()).to_contain("theme")
expect(thinkbackPrompt("latest decision")).to_contain("latest decision")
```

</details>

#### should normalize and apply tags

- Create a session tag state
- Apply a new tag
   - Expected: result.ok is true
   - Expected: result.tag equals `build-ready`
   - Expected: result.state.savedTag equals `build-ready`
   - Expected: formatTagPill("Build Ready") equals `#build-ready`
- Reject an empty tag
   - Expected: empty.ok is false
- Detect an existing tag
   - Expected: duplicate.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a session tag state")
val state = TagCommandState.new("s1", ["release"], "")

step("Apply a new tag")
val result = applyTag("Build Ready", state)
expect(result.ok).to_equal(true)
expect(result.tag).to_equal("build-ready")
expect(result.message).to_contain("tagged")
expect(result.state.savedTag).to_equal("build-ready")
expect(formatTagPill("Build Ready")).to_equal("#build-ready")

step("Reject an empty tag")
val empty = applyTag("   ", state)
expect(empty.ok).to_equal(false)
expect(empty.message).to_contain("Please provide")

step("Detect an existing tag")
val duplicate = applyTag("release", state)
expect(duplicate.ok).to_equal(true)
expect(duplicate.message).to_contain("already tagged")
```

</details>

#### should model theme stickers tasks and source floors

- Resolve theme choices
   - Expected: canonicalTheme("DARK") equals `dark`
   - Expected: canonicalTheme("unknown") equals `system`
- Render small labels
   - Expected: stickerLabel("ship", "*") equals `* ship`
- Check modeled TypeScript source floors
   - Expected: stickersSourceLinesModeled() equals `16`
   - Expected: tagIndexSourceLinesModeled() equals `12`
   - Expected: tagCommandSourceLinesModeled() equals `214`
   - Expected: tasksIndexSourceLinesModeled() equals `11`
   - Expected: tasksSourceLinesModeled() equals `7`
   - Expected: themeIndexSourceLinesModeled() equals `10`
   - Expected: themeSourceLinesModeled() equals `56`
   - Expected: thinkbackIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve theme choices")
expect(canonicalTheme("DARK")).to_equal("dark")
expect(canonicalTheme("unknown")).to_equal("system")
expect(themeStatus("light")).to_contain("light")
expect(themeOptions()).to_contain("dark")

step("Render small labels")
expect(stickerLabel("ship", "*")).to_equal("* ship")
expect(taskSummary(3)).to_contain("3")

step("Check modeled TypeScript source floors")
expect(stickersSourceLinesModeled()).to_equal(16)
expect(tagIndexSourceLinesModeled()).to_equal(12)
expect(tagCommandSourceLinesModeled()).to_equal(214)
expect(tasksIndexSourceLinesModeled()).to_equal(11)
expect(tasksSourceLinesModeled()).to_equal(7)
expect(themeIndexSourceLinesModeled()).to_equal(10)
expect(themeSourceLinesModeled()).to_equal(56)
expect(thinkbackIndexSourceLinesModeled()).to_equal(13)
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
