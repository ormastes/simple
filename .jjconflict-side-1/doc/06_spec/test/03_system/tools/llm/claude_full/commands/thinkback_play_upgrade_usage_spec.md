# Claude Full Thinkback Play, Upgrade, Usage, and Version Commands

> Checks modern SSpec parity for a small command batch.

<!-- sdn-diagram:id=thinkback_play_upgrade_usage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thinkback_play_upgrade_usage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thinkback_play_upgrade_usage_spec -> std
thinkback_play_upgrade_usage_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thinkback_play_upgrade_usage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Thinkback Play, Upgrade, Usage, and Version Commands

Checks modern SSpec parity for a small command batch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/thinkback_play_upgrade_usage_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for a small command batch.

## Scenarios

### Claude full thinkback play upgrade usage commands

#### should expose command names

- Read command names
   - Expected: thinkbackPlayIndexName() equals `thinkback-play`
   - Expected: thinkbackPlayCommandName() equals `thinkback-play`
   - Expected: upgradeIndexName() equals `upgrade`
   - Expected: upgradeCommandName() equals `upgrade`
   - Expected: usageIndexName() equals `usage`
   - Expected: usageCommandName() equals `usage`
   - Expected: versionCommandName() equals `version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read command names")
expect(thinkbackPlayIndexName()).to_equal("thinkback-play")
expect(thinkbackPlayCommandName()).to_equal("thinkback-play")
expect(upgradeIndexName()).to_equal("upgrade")
expect(upgradeCommandName()).to_equal("upgrade")
expect(usageIndexName()).to_equal("usage")
expect(usageCommandName()).to_equal("usage")
expect(versionCommandName()).to_equal("version")
```

</details>

#### should summarize command behavior

- Build thinkback replay summaries
- Resolve upgrade and usage status
   - Expected: upgradeChannel("INSIDERS") equals `insiders`
   - Expected: upgradeChannel("bad") equals `stable`
   - Expected: shouldPromptForRestart("1.0.0", "1.0.1") is true
   - Expected: shouldPromptForRestart("1.0.0", "1.0.0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build thinkback replay summaries")
val replay = ThinkbackPlayRequest.new("tb-1", "quiet")
expect(thinkbackPlaySummary(replay)).to_contain("tb-1")
expect(thinkbackPlaySummary(replay)).to_contain("quiet")
expect(thinkbackPlaySummary(ThinkbackPlayRequest.new("", ""))).to_contain("No thinkback")

step("Resolve upgrade and usage status")
expect(upgradeChannel("INSIDERS")).to_equal("insiders")
expect(upgradeChannel("bad")).to_equal("stable")
expect(upgradeSummary("latest")).to_contain("latest")
expect(shouldPromptForRestart("1.0.0", "1.0.1")).to_equal(true)
expect(shouldPromptForRestart("1.0.0", "1.0.0")).to_equal(false)
expect(usageSummary(42)).to_contain("42")
expect(versionSummary("1.2.3", "abc")).to_contain("1.2.3")
```

</details>

#### should check modeled TypeScript source floors

- Read modeled source line helpers
   - Expected: thinkbackPlayIndexSourceLinesModeled() equals `17`
   - Expected: thinkbackPlaySourceLinesModeled() equals `43`
   - Expected: upgradeIndexSourceLinesModeled() equals `16`
   - Expected: upgradeSourceLinesModeled() equals `37`
   - Expected: usageIndexSourceLinesModeled() equals `9`
   - Expected: usageSourceLinesModeled() equals `6`
   - Expected: versionSourceLinesModeled() equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read modeled source line helpers")
expect(thinkbackPlayIndexSourceLinesModeled()).to_equal(17)
expect(thinkbackPlaySourceLinesModeled()).to_equal(43)
expect(upgradeIndexSourceLinesModeled()).to_equal(16)
expect(upgradeSourceLinesModeled()).to_equal(37)
expect(usageIndexSourceLinesModeled()).to_equal(9)
expect(usageSourceLinesModeled()).to_equal(6)
expect(versionSourceLinesModeled()).to_equal(22)
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
