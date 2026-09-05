# Claude Full Plugin Marketplace Commands

> Checks first plugin marketplace command files without exercising settings IO.

<!-- sdn-diagram:id=plugin_marketplace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_marketplace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_marketplace_spec -> std
plugin_marketplace_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_marketplace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Marketplace Commands

Checks first plugin marketplace command files without exercising settings IO.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_marketplace_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks first plugin marketplace command files without exercising settings IO.

## Scenarios

### Claude full plugin marketplace command files

#### should add marketplace requests with source, scope, and cache parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val github = addMarketplaceRun(AddMarketplaceRequest.new("anthropics/claude-code-plugins", "", "", ["tools"], false, false))
expect(github.ok).to_equal(true)
expect(github.marketplaceName).to_equal("claude-code-plugins")
expect(github.sourceKind).to_equal("github")
expect(github.scope).to_equal("user")
expect(github.cacheCleared).to_equal(true)
expect(github.eventName).to_equal("tengu_marketplace_added:github")
expect(github.message).to_contain("Successfully added marketplace")
```

</details>

#### should reject invalid add marketplace options

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val badScope = addMarketplaceRun(AddMarketplaceRequest.new("owner/repo", "github", "team", [], false, false))
expect(badScope.ok).to_equal(false)
expect(badScope.message).to_contain("Invalid scope")

val sparseUrl = addMarketplaceRun(AddMarketplaceRequest.new("https://example.com/marketplace.json", "url", "", ["one"], false, false))
expect(sparseUrl.ok).to_equal(false)
expect(sparseUrl.message).to_contain("--sparse is only supported")

val badSource = addMarketplaceRun(AddMarketplaceRequest.new("not a source", "", "", [], false, false))
expect(badSource.ok).to_equal(false)
expect(badSource.message).to_contain("Invalid marketplace source format")
```

</details>

#### should browse configured marketplaces in human and JSON forms

- BrowseMarketplaceRecord new
- BrowseMarketplaceRecord new
   - Expected: browseMarketplaceHuman([]) equals `No marketplaces configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    BrowseMarketplaceRecord.new("core", "github", "anthropics/core", "/tmp/core", ["lint", "review"]),
    BrowseMarketplaceRecord.new("local", "directory", "./plugins", "/tmp/local", ["team"]),
]
expect(browseMarketplaceHuman([])).to_equal("No marketplaces configured")
expect(browseMarketplaceHuman(records)).to_contain("GitHub (anthropics/core)")
expect(browseMarketplaceHuman(records)).to_contain("Directory (./plugins)")
expect(browseMarketplaceJson(records)).to_contain("\"installLocation\":\"/tmp/core\"")
```

</details>

#### should expose available marketplace plugins excluding installed ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [BrowseMarketplaceRecord.new("core", "github", "anthropics/core", "/tmp/core", ["lint", "review"])]
val available = browseMarketplaceAvailable(records, ["lint@core"])
expect(available.len()).to_equal(1)
expect(available[0].pluginId).to_equal("review@core")
expect(browseMarketplaceAvailableJson(records, ["lint@core"])).to_contain("\"marketplaceName\":\"core\"")
```

</details>

#### should preserve source line floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(addMarketplaceSourceLinesModeled()).to_equal(161)
expect(browseMarketplaceSourceLinesModeled()).to_equal(801)
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
