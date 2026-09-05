# Claude Full CLI Auto Mode Handler

> Checks auto-mode defaults/config/critique formatting.

<!-- sdn-diagram:id=autoMode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=autoMode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

autoMode_spec -> std
autoMode_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=autoMode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Auto Mode Handler

Checks auto-mode defaults/config/critique formatting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks auto-mode defaults/config/critique formatting.

## Scenarios

### Claude full cli auto mode handler

#### writes default rules

- Defaults command dumps JSON-style rules
   - Expected: autoModeDefaultsHandler(defaults) equals `writeRules(defaults)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Defaults command dumps JSON-style rules")
val defaults = AutoModeRules.new(["read"], ["delete"], ["linux"])
expect(autoModeDefaultsHandler(defaults)).to_equal(writeRules(defaults))
expect(autoModeDefaultsHandler(defaults)).to_contain("\"allow\":[\"read\"]")
```

</details>

#### merges config with per-section replace semantics

- Non-empty user section replaces that section, empty falls back to defaults
   - Expected: merged.permit equals `["write"]`
   - Expected: merged.soft_deny equals `["delete"]`
   - Expected: merged.environment equals `["linux"]`
   - Expected: autoModeConfigHandler(Some(config), defaults) equals `writeRules(merged)`
   - Expected: autoModeConfigHandler(nil, defaults) equals `writeRules(defaults)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Non-empty user section replaces that section, empty falls back to defaults")
val defaults = AutoModeRules.new(["read"], ["delete"], ["linux"])
val config = AutoModeRules.new(["write"], [], [])
val merged = mergeAutoModeRules(config, defaults)
expect(merged.permit).to_equal(["write"])
expect(merged.soft_deny).to_equal(["delete"])
expect(merged.environment).to_equal(["linux"])
expect(autoModeConfigHandler(Some(config), defaults)).to_equal(writeRules(merged))
expect(autoModeConfigHandler(nil, defaults)).to_equal(writeRules(defaults))
```

</details>

#### formats custom rules for critique

- Only non-empty custom sections are included
   - Expected: formatRulesForCritique("soft_deny", [], defaults.soft_deny) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only non-empty custom sections are included")
val defaults = AutoModeRules.new(["read"], ["delete"], ["linux"])
val config = AutoModeRules.new(["write"], [], ["mac"])
val permitText = formatRulesForCritique("allow", config.permit, defaults.permit)
expect(permitText).to_contain("## allow (custom rules replacing defaults)")
expect(permitText).to_contain("- write")
expect(permitText).to_contain("- read")
expect(formatRulesForCritique("soft_deny", [], defaults.soft_deny)).to_equal("")
expect(formatAllRulesForCritique(config, defaults)).to_contain("## environment")
```

</details>

#### handles critique without custom rules

- No custom rules returns guidance and does not call side query
   - Expected: result.stdout equals `noCustomRulesMessage()`
   - Expected: result.model equals ``
   - Expected: result.querySource equals `sideQuerySource()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("No custom rules returns guidance and does not call side query")
val result = autoModeCritiqueHandler(AutoModeRules.empty(), AutoModeRules.new(["read"], ["delete"], ["linux"]), "", "main", true, "")
expect(result.stdout).to_equal(noCustomRulesMessage())
expect(result.model).to_equal("")
expect(result.querySource).to_equal(sideQuerySource())
```

</details>

#### builds critique request and handles responses

- Model option is parsed, side query text is printed, empty text gets fallback
   - Expected: ok.model equals `parseUserSpecifiedModel("opus")`
   - Expected: ok.stdout equals `analyzingMessage() + "Looks good.\n"`
   - Expected: empty.stdout equals `noCritiqueGeneratedMessage()`
   - Expected: failed.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Model option is parsed, side query text is printed, empty text gets fallback")
val defaults = AutoModeRules.new(["read"], ["delete"], ["linux"])
val config = AutoModeRules.new(["write"], [], [])
val ok = autoModeCritiqueHandler(config, defaults, "opus", "main", true, "Looks good.")
expect(ok.model).to_equal(parseUserSpecifiedModel("opus"))
expect(ok.stdout).to_equal(analyzingMessage() + "Looks good.\n")
expect(ok.userMessage).to_contain(classifierPromptTag())
expect(ok.userMessage).to_contain("Please critique these custom rules.")
val empty = autoModeCritiqueHandler(config, defaults, "", "main", true, "")
expect(empty.stdout).to_equal(noCritiqueGeneratedMessage())
val failed = autoModeCritiqueHandler(config, defaults, "", "main", false, "")
expect(failed.exitCode).to_equal(1)
expect(failed.stderr).to_contain(failedAnalyzePrefix())
```

</details>

#### exports source-backed constants

- Pin command names, section names, and side-query options
   - Expected: defaultsCommandName() equals `defaults`
   - Expected: configCommandName() equals `config`
   - Expected: critiqueCommandName() equals `critique`
   - Expected: critiqueMaxTokens() equals `4096`
   - Expected: skipSystemPromptPrefix() is true
   - Expected: permitSectionName() equals `allow`
   - Expected: softDenySectionName() equals `soft_deny`
   - Expected: environmentSectionName() equals `environment`
   - Expected: userSettingsPathHint() equals `autoMode.{allow, soft_deny, environment}`
   - Expected: defaultRulesReferenceCommand() equals `claude auto-mode defaults`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin command names, section names, and side-query options")
expect(defaultsCommandName()).to_equal("defaults")
expect(configCommandName()).to_equal("config")
expect(critiqueCommandName()).to_equal("critique")
expect(critiqueSystemPrompt()).to_contain("expert reviewer")
expect(critiqueMaxTokens()).to_equal(4096)
expect(skipSystemPromptPrefix()).to_equal(true)
expect(permitSectionName()).to_equal("allow")
expect(softDenySectionName()).to_equal("soft_deny")
expect(environmentSectionName()).to_equal("environment")
expect(replaceSemantics()).to_contain("replaces defaults")
expect(userSettingsPathHint()).to_equal("autoMode.{allow, soft_deny, environment}")
expect(defaultRulesReferenceCommand()).to_equal("claude auto-mode defaults")
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
