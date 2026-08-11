# Claude Full LogoV2 Main Component

> Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

<!-- sdn-diagram:id=logo_v2_main_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logo_v2_main_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logo_v2_main_spec -> std
logo_v2_main_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logo_v2_main_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogoV2 Main Component

Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

## Scenarios

### Claude full LogoV2 main component

#### should render condensed mode when no full-logo triggers are active

- Build default condensed input
   - Expected: render.mode equals `condensed`
   - Expected: render.logo equals `CondensedLogo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build default condensed input")
val input = logoV2DefaultInput()
val render = LogoV2(input)
expect(render.mode).to_equal("condensed")
expect(render.logo).to_equal("CondensedLogo")
expect(render.summary()).to_contain("Claude Code")
```

</details>

#### should render compact mode with sandbox and tmux notices

- Build compact input
   - Expected: render.mode equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build compact input")
val config = LogoV2Config.new("Ada", "Acme", 2, "1.0.0", "dark", ["Deploy window"])
val display = LogoDisplayData.new("1.2.0", "/repo/simple", "team", "ops")
val flags = LogoV2Flags.new(true, false, true, false, false, false, true, true, false, false, false, false, "work", "C-a", true)
val input = LogoV2Input.new(60, config, display, flags, ["compile"], ["new-ui"], [], "opus", "Claude Opus", "high", "", "/tmp/debug.log", "/tmp/prompts", "/tmp/startup",)
val render = LogoV2(input)
expect(render.mode).to_equal("compact")
expect(render.welcome).to_contain("Ada")
expect(render.summary()).to_contain("sandboxed")
expect(render.summary()).to_contain("ChannelsNotice")
```

</details>

#### should render full feed names and effects

- Build horizontal full input
   - Expected: render.mode equals `horizontal`
   - Expected: render.feed_names[0] equals `recent-activity:2`
   - Expected: render.feed_names[1] equals `guest-passes`
   - Expected: render.increment_guest_passes_seen is true
   - Expected: render.increment_overage_credit_seen is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build horizontal full input")
val config = LogoV2Config.new("Grace", "Research", 3, "1.0.0", "system", ["Announcement"])
val display = LogoDisplayData.new("1.3.0", "/home/work/project", "enterprise", "mentor")
val flags = LogoV2Flags.new(true, false, false, true, true, true, false, false, false, true, false, false, "", "", false)
val input = LogoV2Input.new(140, config, display, flags, ["a", "b"], ["c"], ["setup"], "sonnet", "Claude Sonnet", "medium", "coder", "/tmp/debug.log", "/tmp/prompts", "/tmp/startup",)
val render = LogoV2(input)
expect(render.mode).to_equal("horizontal")
expect(render.feed_names[0]).to_equal("recent-activity:2")
expect(render.feed_names[1]).to_equal("guest-passes")
expect(render.increment_guest_passes_seen).to_equal(true)
expect(render.increment_overage_credit_seen).to_equal(false)
```

</details>

#### should check modeled TypeScript source floor

- Read source line helper
   - Expected: logoV2SourceLinesModeled() equals `542`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helper")
expect(logoV2SourceLinesModeled()).to_equal(542)
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
