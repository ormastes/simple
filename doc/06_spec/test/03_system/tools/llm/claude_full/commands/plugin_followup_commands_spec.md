# Claude Full Plugin Followup Commands

> Checks modern SSpec parity for pagination and command followups.

<!-- sdn-diagram:id=plugin_followup_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_followup_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_followup_commands_spec -> std
plugin_followup_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_followup_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Followup Commands

Checks modern SSpec parity for pagination and command followups.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_followup_commands_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for pagination and command followups.

## Scenarios

### Claude full plugin followup commands

#### should paginate plugin rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = PaginationState.new(2, 10, 21)
expect(paginationTotalPages(page)).to_equal(3)
expect(paginationCanNext(page)).to_equal(true)
expect(paginationCanPrevious(page)).to_equal(true)
```

</details>

#### should expose command behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(prCommentsSummary(3)).to_contain("3")
expect(privacySettingsSummary(PrivacySettings.new(true, false))).to_contain("telemetry=true")
expect(rateLimitOptionLabel(defaultRateLimitOptions()[0])).to_equal("wait:60")
expect(releaseNotesUrl("v1")).to_contain("v1")
expect(reloadPluginsResult(2).message).to_contain("2")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(usePaginationSourceLinesModeled()).to_equal(171)
expect(prCommentsIndexSourceLinesModeled()).to_equal(50)
expect(privacySettingsSourceLinesModeled()).to_equal(57)
expect(privacySettingsIndexSourceLinesModeled()).to_equal(14)
expect(rateLimitOptionsSourceLinesModeled()).to_equal(209)
expect(rateLimitOptionsIndexSourceLinesModeled()).to_equal(19)
expect(releaseNotesSourceLinesModeled()).to_equal(50)
expect(releaseNotesIndexSourceLinesModeled()).to_equal(11)
expect(reloadPluginsSourceLinesModeled()).to_equal(61)
expect(reloadPluginsIndexSourceLinesModeled()).to_equal(18)
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
