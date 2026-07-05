# Claude Full LogoV2 Condensed and Overage Components

> Modern SSpec coverage for worker-owned LogoV2 condensed logo and overage credit helpers.

<!-- sdn-diagram:id=logo_v2_condensed_overage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logo_v2_condensed_overage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logo_v2_condensed_overage_spec -> std
logo_v2_condensed_overage_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logo_v2_condensed_overage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogoV2 Condensed and Overage Components

Modern SSpec coverage for worker-owned LogoV2 condensed logo and overage credit helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/logo_v2_condensed_overage_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for worker-owned LogoV2 condensed logo and overage credit helpers.

## Scenarios

### Claude full LogoV2 condensed logo and overage credit

#### should render condensed logo rows

- Render condensed logo with guest passes
   - Expected: render.logo equals `Clawd`
   - Expected: render.guestPassesUpsellVisible is true
   - Expected: render.overageCreditUpsellVisible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render condensed logo with guest passes")
val input = CondensedLogoInput.new(80, "agent-a", "high", "opus", "Claude Opus", "1.2.3", "/tmp/project", "monthly", "", true, true, false)
val render = CondensedLogo(input)
expect(render.logo).to_equal("Clawd")
expect(render.guestPassesUpsellVisible).to_equal(true)
expect(render.overageCreditUpsellVisible).to_equal(false)
expect(render.summary()).to_contain("Claude Code v1.2.3")
```

</details>

#### should render overage credit eligibility and display

- Configure eligible overage credit
- setCachedOverageCreditGrant
- setOverageCreditConfig
   - Expected: shouldShowOverageCreditUpsell() is true
- Render two-line overage credit
   - Expected: render.visible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure eligible overage credit")
setCachedOverageCreditGrant(OverageCreditGrantInfo.new(true, false, "25", "usd"))
setOverageCreditConfig(OverageCreditConfig.new(false, 1))
expect(shouldShowOverageCreditUpsell()).to_equal(true)

step("Render two-line overage credit")
val render = OverageCreditUpsell(Props.new(40, true))
expect(render.visible).to_equal(true)
expect(render.summary()).to_contain("$25 in extra usage")
```

</details>

#### should track overage impressions

- Increment seen count
- setOverageCreditConfig
- incrementOverageCreditUpsellSeenCount
   - Expected: overageCreditLastAnalyticsSeenCount() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Increment seen count")
setOverageCreditConfig(OverageCreditConfig.new(false, 0))
incrementOverageCreditUpsellSeenCount()
expect(overageCreditLastAnalyticsSeenCount()).to_equal(1)
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: condensedLogoSourceLinesModeled() equals `160`
   - Expected: overageCreditSourceLinesModeled() equals `165`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(condensedLogoSourceLinesModeled()).to_equal(160)
expect(overageCreditSourceLinesModeled()).to_equal(165)
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
