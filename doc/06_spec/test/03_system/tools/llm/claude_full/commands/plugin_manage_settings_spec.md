# Claude Full Plugin Manage/Settings Commands

> Checks plugin manage and settings parity models without settings IO.

<!-- sdn-diagram:id=plugin_manage_settings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_manage_settings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_manage_settings_spec -> std
plugin_manage_settings_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_manage_settings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Manage/Settings Commands

Checks plugin manage and settings parity models without settings IO.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks plugin manage and settings parity models without settings IO.

## Scenarios

### Claude full plugin manage and settings command files

#### should model manage plugin lists, search, and toggles

- ManagedPluginInfo new
- ManagedPluginInfo new
- ManagedPluginInfo new
   - Expected: managePluginsEnabledCount(plugins) equals `2`
   - Expected: managePluginsFilterDisabled(plugins).len() equals `1`
   - Expected: managePluginsSearch(plugins, "review")[0].pluginId equals `review@core`
   - Expected: managePluginsMcpStatus(plugins[0]) equals `enabled`
   - Expected: managePluginsScopeLabel("project") equals `Project`
   - Expected: toggled.ok is true
   - Expected: toggled.enabled is true
   - Expected: toggled.cacheCleared is true
   - Expected: toggled.eventName equals `tengu_plugin_enabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plugins = [
    ManagedPluginInfo.new("lint@core", "lint", "user", true, false, "core", true, false),
    ManagedPluginInfo.new("review@core", "review", "project", false, false, "core", false, false),
    ManagedPluginInfo.new("local-tools", "local tools", "local", true, true, "", false, false),
]
expect(managePluginsEnabledCount(plugins)).to_equal(2)
expect(managePluginsFilterDisabled(plugins).len()).to_equal(1)
expect(managePluginsSearch(plugins, "review")[0].pluginId).to_equal("review@core")
expect(managePluginsMcpStatus(plugins[0])).to_equal("enabled")
expect(managePluginsScopeLabel("project")).to_equal("Project")

val toggled = managePluginsToggle(plugins[1])
expect(toggled.ok).to_equal(true)
expect(toggled.enabled).to_equal(true)
expect(toggled.cacheCleared).to_equal(true)
expect(toggled.eventName).to_equal("tengu_plugin_enabled")
```

</details>

#### should protect local plugins and failed plugins

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local = ManagedPluginInfo.new("local-tools", "local tools", "local", true, true, "", false, false)
val failed = ManagedPluginInfo.new("bad@core", "bad", "user", false, false, "core", true, true)
expect(managePluginsUninstall(local).ok).to_equal(false)
expect(managePluginsUninstall(local).message).to_contain("Local plugins cannot be uninstalled")
expect(managePluginsToggle(failed).ok).to_equal(false)
expect(managePluginsMcpStatus(failed)).to_equal("error")
```

</details>

#### should derive component names from plugin paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = ["/tmp/plugin/commands/foo.md", "/tmp/plugin/skills/review", "README.md"]
expect(managePluginsGetBaseFileNames(paths)[0]).to_equal("foo.md")
expect(managePluginsGetSkillDirNames(["/tmp/plugin/skills/review", "/tmp/plugin/skills/SKILL.md"]).len()).to_equal(1)
```

</details>

#### should model settings marketplace actions and error rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marketplace = PluginSettingsMarketplace.new("core", "github", "anthropics/core", "user")
expect(pluginSettingsMarketplaceSourceInfo(marketplace)).to_equal("GitHub (anthropics/core)")
val action = pluginSettingsBuildMarketplaceAction(marketplace)
expect(action.command).to_equal("remove-marketplace:core:user")
expect(action.destructive).to_equal(true)
expect(pluginSettingsBuildPluginAction("lint@core", true).command).to_equal("disable-plugin:lint@core")

val rows = pluginSettingsBuildErrorRows(["plugin lint@core timeout while loading", "bad manifest"])
expect(rows.len()).to_equal(2)
expect(rows[0].pluginName).to_equal("lint@core")
expect(rows[0].transient).to_equal(true)
expect(rows[1].pluginName).to_equal("")
```

</details>

#### should remove extra marketplaces and choose initial tab

- PluginSettingsMarketplace new
- PluginSettingsMarketplace new
   - Expected: pluginSettingsRemoveMarketplace(marketplaces, "core").len() equals `1`
   - Expected: pluginSettingsInitialViewState(true).tab equals `errors`
   - Expected: pluginSettingsInitialViewState(false).tab equals `plugins`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marketplaces = [
    PluginSettingsMarketplace.new("core", "github", "anthropics/core", "user"),
    PluginSettingsMarketplace.new("local", "directory", "./plugins", "project"),
]
expect(pluginSettingsRemoveMarketplace(marketplaces, "core").len()).to_equal(1)
expect(pluginSettingsInitialViewState(true).tab).to_equal("errors")
expect(pluginSettingsInitialViewState(false).tab).to_equal("plugins")
```

</details>

#### should preserve source line floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(managePluginsSourceLinesModeled()).to_equal(2214)
expect(pluginSettingsSourceLinesModeled()).to_equal(1071)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
