# Claude Full Plugin Manage/Settings Commands

> Purpose: should model manage plugin lists, search, and toggles

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Manage/Settings Commands

Purpose: should model manage plugin lists, search, and toggles

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should model manage plugin lists, search, and toggles
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Plugin Manage/Settings Commands

Checks plugin manage and settings parity models without settings IO.

## Scenarios

### Claude full plugin manage and settings command files

#### should model manage plugin lists, search, and toggles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model manage plugin lists, search, and toggles
- Verify: should model manage plugin lists, search, and toggles
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

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model manage plugin lists, search, and toggles")
step("Verify: should model manage plugin lists, search, and toggles")
# @req: REQ-TOOLS-PlugManaSett-001
val plugins = [
    ManagedPluginInfo.new("lint@core", "lint", "user", true, false, "core", true, false),
    ManagedPluginInfo.new("review@core", "review", "project", false, false, "core", false, false),
    ManagedPluginInfo.new("local-tools", "local tools", "local", true, true, "", false, false),
]
expect(managePluginsEnabledCount(plugins)).to_equal(2)  # oracle: value fixed by the spec contract
expect(managePluginsFilterDisabled(plugins).len()).to_equal(1)  # oracle: value fixed by the spec contract
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

- should protect local plugins and failed plugins
- Verify: should protect local plugins and failed plugins
   - Expected: managePluginsUninstall(local).ok is false
   - Expected: managePluginsToggle(failed).ok is false
   - Expected: managePluginsMcpStatus(failed) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should protect local plugins and failed plugins")
step("Verify: should protect local plugins and failed plugins")
# @req: REQ-TOOLS-PlugManaSett-001
val local = ManagedPluginInfo.new("local-tools", "local tools", "local", true, true, "", false, false)
val failed = ManagedPluginInfo.new("bad@core", "bad", "user", false, false, "core", true, true)
expect(managePluginsUninstall(local).ok).to_equal(false)
expect(managePluginsUninstall(local).message).to_contain("Local plugins cannot be uninstalled")
expect(managePluginsToggle(failed).ok).to_equal(false)
expect(managePluginsMcpStatus(failed)).to_equal("error")
```

</details>

#### should derive component names from plugin paths

- should derive component names from plugin paths
- Verify: should derive component names from plugin paths
   - Expected: managePluginsGetBaseFileNames(paths)[0] equals `foo.md`
   - Expected: managePluginsGetSkillDirNames(["/tmp/plugin/skills/review", "/tmp/plugin/skills/SKILL.md"]).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive component names from plugin paths")
step("Verify: should derive component names from plugin paths")
# @req: REQ-TOOLS-PlugManaSett-001
val paths = ["/tmp/plugin/commands/foo.md", "/tmp/plugin/skills/review", "README.md"]
expect(managePluginsGetBaseFileNames(paths)[0]).to_equal("foo.md")
expect(managePluginsGetSkillDirNames(["/tmp/plugin/skills/review", "/tmp/plugin/skills/SKILL.md"]).len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should model settings marketplace actions and error rows

- should model settings marketplace actions and error rows
- Verify: should model settings marketplace actions and error rows
   - Expected: pluginSettingsMarketplaceSourceInfo(marketplace) equals `GitHub (anthropics/core)`
   - Expected: action.command equals `remove-marketplace:core:user`
   - Expected: action.destructive is true
   - Expected: pluginSettingsBuildPluginAction("lint@core", true).command equals `disable-plugin:lint@core`
   - Expected: rows.len() equals `2`
   - Expected: rows[0].pluginName equals `lint@core`
   - Expected: rows[0].transient is true
   - Expected: rows[1].pluginName equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model settings marketplace actions and error rows")
step("Verify: should model settings marketplace actions and error rows")
# @req: REQ-TOOLS-PlugManaSett-001
val marketplace = PluginSettingsMarketplace.new("core", "github", "anthropics/core", "user")
expect(pluginSettingsMarketplaceSourceInfo(marketplace)).to_equal("GitHub (anthropics/core)")
val action = pluginSettingsBuildMarketplaceAction(marketplace)
expect(action.command).to_equal("remove-marketplace:core:user")
expect(action.destructive).to_equal(true)
expect(pluginSettingsBuildPluginAction("lint@core", true).command).to_equal("disable-plugin:lint@core")

val rows = pluginSettingsBuildErrorRows(["plugin lint@core timeout while loading", "bad manifest"])
expect(rows.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(rows[0].pluginName).to_equal("lint@core")
expect(rows[0].transient).to_equal(true)
expect(rows[1].pluginName).to_equal("")
```

</details>

#### should remove extra marketplaces and choose initial tab

- should remove extra marketplaces and choose initial tab
- Verify: should remove extra marketplaces and choose initial tab
   - Expected: pluginSettingsRemoveMarketplace(marketplaces, "core").len() equals `1`
   - Expected: pluginSettingsInitialViewState(true).tab equals `errors`
   - Expected: pluginSettingsInitialViewState(false).tab equals `plugins`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should remove extra marketplaces and choose initial tab")
step("Verify: should remove extra marketplaces and choose initial tab")
# @req: REQ-TOOLS-PlugManaSett-001
val marketplaces = [
    PluginSettingsMarketplace.new("core", "github", "anthropics/core", "user"),
    PluginSettingsMarketplace.new("local", "directory", "./plugins", "project"),
]
expect(pluginSettingsRemoveMarketplace(marketplaces, "core").len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(pluginSettingsInitialViewState(true).tab).to_equal("errors")
expect(pluginSettingsInitialViewState(false).tab).to_equal("plugins")
```

</details>

#### should preserve source line floors

- should preserve source line floors
- Verify: should preserve source line floors
   - Expected: managePluginsSourceLinesModeled() equals `2214`
   - Expected: pluginSettingsSourceLinesModeled() equals `1071`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve source line floors")
step("Verify: should preserve source line floors")
# @req: REQ-TOOLS-PlugManaSett-001
expect(managePluginsSourceLinesModeled()).to_equal(2214)  # oracle: value fixed by the spec contract
expect(pluginSettingsSourceLinesModeled()).to_equal(1071)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-PlugManaSett-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ceeb98ff8a488e2d710108aea5ccfc14adb4eaf29d60ca90c97bfe005e4c03f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ceeb98ff8a488e2d710108aea5ccfc14adb4eaf29d60ca90c97bfe005e4c03f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ceeb98ff8a488e2d710108aea5ccfc14adb4eaf29d60ca90c97bfe005e4c03f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model manage plugin lists, search, and toggles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model manage plugin lists, search, and toggles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should protect local plugins and failed plugins' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should protect local plugins and failed plugins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive component names from plugin paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive component names from plugin paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model settings marketplace actions and error rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should remove extra marketplaces and choose initial tab' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/plugin_manage_settings_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve source line floors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
