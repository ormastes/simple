# Claude Full CLI Plugins Handler

> This executable specification pins the `tmp/claude/claude-code-main/src/cli/handlers/plugins.ts` parity slice for plugin validation, plugin listing, marketplace management, and plugin install/uninstall/enable/disable/update command decisions. The Simple implementation models the handler behavior as pure command-result helpers so the system spec can verify the user visible output, analytics event names, scope decisions, inline plugin handling, and cache invalidation without reaching into Claude Code runtime state.

<!-- sdn-diagram:id=plugins_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugins_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugins_spec -> std
plugins_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugins_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Plugins Handler

This executable specification pins the `tmp/claude/claude-code-main/src/cli/handlers/plugins.ts` parity slice for plugin validation, plugin listing, marketplace management, and plugin install/uninstall/enable/disable/update command decisions. The Simple implementation models the handler behavior as pure command-result helpers so the system spec can verify the user visible output, analytics event names, scope decisions, inline plugin handling, and cache invalidation without reaching into Claude Code runtime state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - direct upstream parity slice. |
| Plan | N/A - scoped implementation request. |
| Design | N/A - mirrors adjacent llm_caret claude_full handler parity modules. |
| Research | N/A - source of truth is the checked-in TypeScript handler. |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/plugins_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable specification pins the `tmp/claude/claude-code-main/src/cli/handlers/plugins.ts`
parity slice for plugin validation, plugin listing, marketplace management, and plugin
install/uninstall/enable/disable/update command decisions. The Simple implementation models
the handler behavior as pure command-result helpers so the system spec can verify the user
visible output, analytics event names, scope decisions, inline plugin handling, and cache
invalidation without reaching into Claude Code runtime state.

## Requirements

**Requirements:** N/A - direct upstream parity slice.
**Plan:** N/A - scoped implementation request.
**Design:** N/A - mirrors adjacent llm_caret claude_full handler parity modules.
**Research:** N/A - source of truth is the checked-in TypeScript handler.

## Examples

The scenarios below use `step(...)` evidence and built-in matchers only. They cover validation
success/failure, installed and inline plugin list output, marketplace add/list/remove/update,
plugin lifecycle scope validation, cowork scope behavior, and source-backed behavior flags.

## Scenarios

### Claude full cli plugins handler

#### validates manifests and plugin content

- Successful plugin validation reports warnings when any content warning exists
   - Expected: ok.exitCode equals `0`
   - Expected: ok.coworkEnabled is true
- Validation failures exit as user errors and unexpected exceptions use exit code 2
   - Expected: bad.exitCode equals `1`
   - Expected: pluginValidateUnexpectedError("boom").exitCode equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Successful plugin validation reports warnings when any content warning exists")
val manifest = PluginValidationResult.new("plugin", "/repo/.claude-plugin/plugin.json", true, [], [])
val skill = PluginValidationResult.new("skill", "/repo/skills/a/SKILL.md", true, [], ["description missing"])
val ok = pluginValidateHandler(manifest, [skill], true)
expect(ok.exitCode).to_equal(0)
expect(ok.stdout).to_contain("Validating plugin manifest")
expect(ok.stdout).to_contain("Validating skill")
expect(ok.stdout).to_contain("Validation passed with warnings")
expect(ok.coworkEnabled).to_equal(true)
step("Validation failures exit as user errors and unexpected exceptions use exit code 2")
val bad = pluginValidateHandler(PluginValidationResult.new("marketplace", "/bad.json", false, ["name: required"], []), [], false)
expect(bad.exitCode).to_equal(1)
expect(bad.stderr).to_contain("Validation failed")
expect(pluginValidateUnexpectedError("boom").exitCode).to_equal(2)
```

</details>

#### lists installed plugins in human form

- Installed entries show scope, status, load errors, and empty guidance
   - Expected: pluginListHandler([], [], [], [], [], false, false, false).stdout equals `noPluginsInstalledMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Installed entries show scope, status, load errors, and empty guidance")
expect(pluginListHandler([], [], [], [], [], false, false, false).stdout).to_equal(noPluginsInstalledMessage())
val installed = PluginInstallRecord.new("lint@core", "1.2.0", "user", "/plugins/lint")
val broken = PluginLoadError.new("lint@core", "lint", "", "bad manifest")
val output = pluginListHandler([installed], [], [broken], ["lint@core"], [], false, false, false)
expect(output.stdout).to_contain("Installed plugins:")
expect(output.stdout).to_contain("lint@core")
expect(output.stdout).to_contain("failed to load")
expect(output.stdout).to_contain("bad manifest")
expect(output.events).to_contain(pluginListEventName())
```

</details>

#### lists inline plugins and path-level inline failures

- Session-only plugins are visible even when not installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Session-only plugins are visible even when not installed")
val inline = LoadedPluginRecord.new("dev@inline", "dev", "", "/tmp/dev", true)
val namedError = PluginLoadError.new("checkout@inline", "dev", "", "command failed")
val pathError = PluginLoadError.new("inline[0]", "", "/missing", "directory not found")
val result = pluginListHandler([], [inline], [namedError, pathError], [], [], false, false, false)
expect(result.stdout).to_contain("Session-only plugins (--plugin-dir):")
expect(result.stdout).to_contain("dev@inline")
expect(result.stdout).to_contain("Version: unknown")
expect(result.stdout).to_contain("command failed")
expect(result.stdout).to_contain("inline[0]: ✖ directory not found")
```

</details>

#### lists plugins as JSON with available marketplace entries

- JSON output includes installed metadata, MCP servers, inline errors, and available plugins


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("JSON output includes installed metadata, MCP servers, inline errors, and available plugins")
val installed = PluginInstallRecord.new("installed@market", "2.0.0", "project", "/p/installed")
val loaded = LoadedPluginRecord.new("installed@market", "installed", "2.0.0", "/p/installed", true)
loaded.mcpServers = ["fs"]
val inlineError = PluginLoadError.new("inline[1]", "", "/bad", "missing")
val market = MarketplaceRecord.new("market", "github", "owner/repo")
market.pluginNames = ["installed", "new-one"]
val json = pluginListHandler([installed], [loaded], [inlineError], ["installed@market"], [market], true, true, false).stdout
expect(json).to_contain("\"installed\"")
expect(json).to_contain("\"mcpServers\":[\"fs\"]")
expect(json).to_contain("\"id\":\"inline[1]\"")
expect(json).to_contain("\"available\"")
expect(json).to_contain("new-one@market")
expect(json).to_contain("enabled\":true")
```

</details>

#### adds and lists marketplaces

- Marketplace add validates scope and sparse support, writes intent, and clears caches
   - Expected: add.cacheCleared is true
   - Expected: add.scope equals `project`
- Marketplace list renders source labels and JSON records
   - Expected: marketplaceListHandler([], false, false).stdout equals `noMarketplacesConfiguredMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Marketplace add validates scope and sparse support, writes intent, and clears caches")
val add = marketplaceAddHandler("owner/plugins", "github", "project", ["skills"], false, false)
expect(add.stdout).to_contain("Adding marketplace...")
expect(add.stdout).to_contain("Successfully added marketplace: plugins")
expect(add.events).to_contain(marketplaceAddedEventName() + ":github")
expect(add.cacheCleared).to_equal(true)
expect(add.scope).to_equal("project")
val badSparse = marketplaceAddHandler("https://x/list.json", "url", "user", ["skills"], false, false)
expect(badSparse.stderr).to_contain("--sparse is only supported")
val badScope = marketplaceAddHandler("owner/repo", "github", "team", [], false, false)
expect(badScope.stderr).to_contain("Invalid scope")
step("Marketplace list renders source labels and JSON records")
val record = MarketplaceRecord.new("core", "git", "https://example/core.git")
expect(marketplaceListHandler([], false, false).stdout).to_equal(noMarketplacesConfiguredMessage())
expect(marketplaceListHandler([record], false, false).stdout).to_contain("Source: Git (https://example/core.git)")
expect(marketplaceListHandler([record], true, false).stdout).to_contain("\"source\":\"git\"")
```

</details>

#### removes and updates marketplaces

- Remove and update clear caches after mutating marketplace materialization
   - Expected: removed.cacheCleared is true
   - Expected: removed.coworkEnabled is true
   - Expected: empty.stdout equals `noMarketplacesConfiguredMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove and update clear caches after mutating marketplace materialization")
val removed = marketplaceRemoveHandler("core", true)
expect(removed.stdout).to_contain("Successfully removed marketplace: core")
expect(removed.cacheCleared).to_equal(true)
expect(removed.coworkEnabled).to_equal(true)
val one = marketplaceUpdateHandler("core", 0, false)
expect(one.stdout).to_contain("Updating marketplace: core...")
expect(one.events).to_contain(marketplaceUpdatedEventName() + ":core")
val empty = marketplaceUpdateHandler("", 0, false)
expect(empty.stdout).to_equal(noMarketplacesConfiguredMessage())
val all = marketplaceUpdateHandler("", 3, false)
expect(all.stdout).to_contain("Successfully updated 3 marketplace(s)")
expect(all.events).to_contain(marketplaceUpdatedAllEventName() + ":3")
```

</details>

#### installs, uninstalls, enables, disables, and updates plugins

- Install and uninstall validate installable scopes and log parsed plugin identity
   - Expected: install.scope equals `local`
   - Expected: uninstall.scope equals `defaultPluginScope()`
   - Expected: uninstall.keepData is true
- Cowork uses user scope when omitted and rejects non-user scope
   - Expected: enabled.scope equals `user`
   - Expected: pluginDisableHandler("lint", "project", true, false).stderr equals `--cowork can only be used with user scope`
- Disable all has mutually exclusive arguments and update uses update scopes
   - Expected: pluginDisableHandler("lint", "", false, true).stderr equals `Cannot use --all with a specific plugin`
   - Expected: pluginDisableHandler("", "", false, false).stderr equals `Please specify a plugin name or use --all to disable all plugins`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Install and uninstall validate installable scopes and log parsed plugin identity")
val install = pluginInstallHandler("lint@core", "local", false)
expect(install.scope).to_equal("local")
expect(install.events).to_contain(pluginInstallEventName() + ":lint:core:local")
val uninstall = pluginUninstallHandler("lint@core", "", false, true)
expect(uninstall.scope).to_equal(defaultPluginScope())
expect(uninstall.keepData).to_equal(true)
expect(uninstall.events).to_contain(pluginUninstallEventName() + ":lint:core:user")
expect(pluginInstallHandler("lint", "team", false).stderr).to_contain("Must be one of")
step("Cowork uses user scope when omitted and rejects non-user scope")
val enabled = pluginEnableHandler("lint@core", "", true)
expect(enabled.scope).to_equal("user")
expect(enabled.events).to_contain(pluginEnableEventName() + ":lint:core:user")
expect(pluginDisableHandler("lint", "project", true, false).stderr).to_equal("--cowork can only be used with user scope")
step("Disable all has mutually exclusive arguments and update uses update scopes")
expect(pluginDisableHandler("lint", "", false, true).stderr).to_equal("Cannot use --all with a specific plugin")
expect(pluginDisableHandler("", "", false, false).stderr).to_equal("Please specify a plugin name or use --all to disable all plugins")
expect(pluginDisableHandler("", "", false, true).events).to_contain(pluginDisableEventName() + ":all")
val update = pluginUpdateHandler("lint@core", "project", false)
expect(update.events).to_contain(pluginUpdateEventName() + ":lint:core:project")
expect(pluginUpdateHandler("lint", "local", false).stderr).to_contain("Valid scopes: user, project")
```

</details>

#### exports source-backed constants and behavior flags

- Pin command names, scopes, analytics events, and explicit TS behavior decisions
   - Expected: validInstallableScopes() equals `["user", "project", "local"]`
   - Expected: validUpdateScopes() equals `["user", "project"]`
   - Expected: defaultPluginScope() equals `user`
   - Expected: defaultUpdateScope() equals `user`
   - Expected: handleMarketplaceError("boom", "add marketplace").stderr equals `"✖ Failed to add marketplace: boom")`
   - Expected: parsed.name equals `demo`
   - Expected: parsed.marketplace equals `market`
   - Expected: dynamicImportOnlyWhenPluginCommandRuns() is true
   - Expected: validateAlsoChecksPluginContentsInClaudePluginDir() is true
   - Expected: listSurfacesInlinePlugins() is true
   - Expected: listSurfacesPathLevelInlineErrors() is true
   - Expected: listLoadsMcpServersForJson() is true
   - Expected: availableMarketplaceListExcludesInstalledPlugins() is true
   - Expected: marketplaceAddClearsCaches() is true
   - Expected: marketplaceRemoveClearsCaches() is true
   - Expected: marketplaceUpdateClearsCaches() is true
   - Expected: coworkForcesUserScopeWhenScopeOmitted() is true
   - Expected: disableAllRejectsSpecificPlugin() is true
   - Expected: disableSpecificRequiresPluginName() is true
   - Expected: updateUsesValidUpdateScopesOnly() is true
   - Expected: installAndUninstallUseInstallableScopes() is true
   - Expected: analyticsUsePrivilegedPluginColumns() is true
   - Expected: pluginHandlerSourceLinesModeled() equals `742`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin command names, scopes, analytics events, and explicit TS behavior decisions")
expect(validInstallableScopes()).to_equal(["user", "project", "local"])
expect(validUpdateScopes()).to_equal(["user", "project"])
expect(defaultPluginScope()).to_equal("user")
expect(defaultUpdateScope()).to_equal("user")
expect(handleMarketplaceError("boom", "add marketplace").stderr).to_equal("✖ Failed to add marketplace: boom")
expect(printValidationResult(PluginValidationResult.new("plugin", "p", false, ["path: bad"], ["warn"]))).to_contain("Found 1 error")
val parsed = parsePluginIdentifier("demo@market")
expect(parsed.name).to_equal("demo")
expect(parsed.marketplace).to_equal("market")
expect(dynamicImportOnlyWhenPluginCommandRuns()).to_equal(true)
expect(validateAlsoChecksPluginContentsInClaudePluginDir()).to_equal(true)
expect(listSurfacesInlinePlugins()).to_equal(true)
expect(listSurfacesPathLevelInlineErrors()).to_equal(true)
expect(listLoadsMcpServersForJson()).to_equal(true)
expect(availableMarketplaceListExcludesInstalledPlugins()).to_equal(true)
expect(marketplaceAddClearsCaches()).to_equal(true)
expect(marketplaceRemoveClearsCaches()).to_equal(true)
expect(marketplaceUpdateClearsCaches()).to_equal(true)
expect(coworkForcesUserScopeWhenScopeOmitted()).to_equal(true)
expect(disableAllRejectsSpecificPlugin()).to_equal(true)
expect(disableSpecificRequiresPluginName()).to_equal(true)
expect(updateUsesValidUpdateScopesOnly()).to_equal(true)
expect(installAndUninstallUseInstallableScopes()).to_equal(true)
expect(analyticsUsePrivilegedPluginColumns()).to_equal(true)
expect(pluginHandlerSourceLinesModeled()).to_equal(742)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - direct upstream parity slice.](N/A - direct upstream parity slice.)
- **Plan:** [N/A - scoped implementation request.](N/A - scoped implementation request.)
- **Design:** [N/A - mirrors adjacent llm_caret claude_full handler parity modules.](N/A - mirrors adjacent llm_caret claude_full handler parity modules.)
- **Research:** [N/A - source of truth is the checked-in TypeScript handler.](N/A - source of truth is the checked-in TypeScript handler.)


</details>
