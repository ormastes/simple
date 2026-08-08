# Claude Full Plugin Discovery And Marketplace Management

> Checks large plugin management parity models without touching settings IO.

<!-- sdn-diagram:id=plugin_discovery_marketplaces_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_discovery_marketplaces_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_discovery_marketplaces_spec -> std
plugin_discovery_marketplaces_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_discovery_marketplaces_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Discovery And Marketplace Management

Checks large plugin management parity models without touching settings IO.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_discovery_marketplaces_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks large plugin management parity models without touching settings IO.

## Scenarios

### Claude full plugin discovery and marketplace management files

#### should discover plugins with filters and render JSON

- DiscoverPluginRecord new
- DiscoverPluginRecord new
- DiscoverPluginRecord new
   - Expected: found.len() equals `1`
   - Expected: found[0].pluginId equals `review@core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    DiscoverPluginRecord.new("review", "core", "github", false, true, "1.0.0"),
    DiscoverPluginRecord.new("lint", "core", "github", true, true, "1.0.0"),
    DiscoverPluginRecord.new("draft", "team", "directory", false, false, "0.2.0"),
]
val query = DiscoverPluginsQuery.new("review", "core", false, true)
val found = discoverPluginsFilter(records, query)
expect(found.len()).to_equal(1)
expect(found[0].pluginId).to_equal("review@core")
expect(discoverPluginsHuman(records, query)).to_contain("review@core")
expect(discoverPluginsJson(records, query)).to_contain("false")
```

</details>

#### should manage marketplace list, removal, and enable state

- ManagedMarketplace new
- ManagedMarketplace new
   - Expected: enabledList does not contain `team [project]`
   - Expected: removed.ok is true
   - Expected: removed.cacheCleared is true
   - Expected: removed.eventName equals `tengu_marketplace_removed`
   - Expected: disabled.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    ManagedMarketplace.new("core", "github", "anthropics/core", "user", true),
    ManagedMarketplace.new("team", "directory", "./plugins", "project", false),
]
val enabledList = manageMarketplacesList(records, false)
expect(enabledList).to_contain("core [user]")
expect(enabledList.contains("team [project]")).to_equal(false)
expect(manageMarketplacesJson(records, true)).to_contain("false")

val removed = manageMarketplacesRemove(records, "core", "user")
expect(removed.ok).to_equal(true)
expect(removed.cacheCleared).to_equal(true)
expect(removed.eventName).to_equal("tengu_marketplace_removed")

val disabled = manageMarketplacesSetEnabled(records, "core", "user", false)
expect(disabled.ok).to_equal(true)
expect(disabled.message).to_contain("Disabled marketplace")
```

</details>

#### should reject invalid marketplace management operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [ManagedMarketplace.new("core", "github", "anthropics/core", "user", true)]
val badScope = manageMarketplacesRemove(records, "core", "team")
expect(badScope.ok).to_equal(false)
expect(badScope.message).to_contain("Invalid scope")

val missing = manageMarketplacesSetEnabled(records, "missing", "user", true)
expect(missing.ok).to_equal(false)
expect(missing.message).to_contain("Marketplace not found")
```

</details>

#### should preserve source line floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(discoverPluginsSourceLinesModeled()).to_equal(780)
expect(manageMarketplacesSourceLinesModeled()).to_equal(837)
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
