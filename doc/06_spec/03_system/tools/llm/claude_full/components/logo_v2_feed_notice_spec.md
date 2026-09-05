# Claude Full LogoV2 Feed and Notice Components

> Modern SSpec coverage for LogoV2 feed, notice, and upsell helpers.

<!-- sdn-diagram:id=logo_v2_feed_notice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logo_v2_feed_notice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logo_v2_feed_notice_spec -> std
logo_v2_feed_notice_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logo_v2_feed_notice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogoV2 Feed and Notice Components

Modern SSpec coverage for LogoV2 feed, notice, and upsell helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/logo_v2_feed_notice_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for LogoV2 feed, notice, and upsell helpers.

## Scenarios

### Claude full LogoV2 feed and notice components

#### should render emergency and voice notices

- Render emergency tip defaults
   - Expected: emergencyTipVisible(emergency) is true
- Render muted voice mode notice
   - Expected: voiceModeNoticeTone(voice) equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render emergency tip defaults")
val emergency = EmergencyTipState.new("", "", true)
expect(emergencyTipVisible(emergency)).to_equal(true)
expect(emergencyTipSummary(emergency)).to_contain("Esc Esc")

step("Render muted voice mode notice")
val voice = VoiceModeNoticeState.new(true, true, "Studio Mic")
expect(voiceModeNoticeTone(voice)).to_equal("warning")
expect(voiceModeNoticeSummary(voice)).to_contain("Studio Mic")
```

</details>

#### should render feed config and feed state

- Normalize feed config
   - Expected: feedConfigEnabledCount(configs) equals `3`
- Render feed column and feed
   - Expected: feedColumnWidth(column.width) equals `16`
   - Expected: feedUnreadCount(state) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize feed config")
val configs = defaultFeedConfigs()
expect(feedConfigEnabledCount(configs)).to_equal(3)
expect(feedConfigSummary(configs[0])).to_contain("Updates")

step("Render feed column and feed")
val column = FeedColumnState.new("", 8, 1, true)
expect(feedColumnWidth(column.width)).to_equal(16)
val state = FeedState.new(configs[0], [FeedItem.new("a", "Release", "Ready", true)], false)
expect(feedUnreadCount(state)).to_equal(1)
expect(renderFeed(state)).to_contain("Release")
```

</details>

#### should render upsell and merge notices

- Render guest passes upsell
   - Expected: guestPassesUpsellVisible(guest) is true
   - Expected: guestPassesUpsellAction(guest) equals `Invite teammate`
- Render Opus merge notice
   - Expected: opus1mMergeNoticeVisible(merge) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render guest passes upsell")
val guest = GuestPassesUpsellState.new(2, false, "team")
expect(guestPassesUpsellVisible(guest)).to_equal(true)
expect(guestPassesUpsellAction(guest)).to_equal("Invite teammate")

step("Render Opus merge notice")
val merge = Opus1mMergeNoticeState.new(true, "", false)
expect(opus1mMergeNoticeVisible(merge)).to_equal(true)
expect(opus1mMergeNoticeSummary(merge)).to_contain("available")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: emergencyTipSourceLinesModeled() equals `57`
   - Expected: feedColumnSourceLinesModeled() equals `58`
   - Expected: feedConfigsSourceLinesModeled() equals `91`
   - Expected: feedSourceLinesModeled() equals `111`
   - Expected: guestPassesUpsellSourceLinesModeled() equals `69`
   - Expected: opus1mMergeNoticeSourceLinesModeled() equals `54`
   - Expected: voiceModeNoticeSourceLinesModeled() equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(emergencyTipSourceLinesModeled()).to_equal(57)
expect(feedColumnSourceLinesModeled()).to_equal(58)
expect(feedConfigsSourceLinesModeled()).to_equal(91)
expect(feedSourceLinesModeled()).to_equal(111)
expect(guestPassesUpsellSourceLinesModeled()).to_equal(69)
expect(opus1mMergeNoticeSourceLinesModeled()).to_equal(54)
expect(voiceModeNoticeSourceLinesModeled()).to_equal(67)
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
