# Claude Full CLI Auto Mode Handler

> Checks auto-mode defaults/config/critique formatting.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks auto-mode defaults/config/critique formatting.

## Scenarios

### Claude full cli auto mode handler

#### writes default rules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes default rules
- Defaults command dumps JSON-style rules
   - Expected: autoModeDefaultsHandler(defaults) equals `writeRules(defaults)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes default rules")
step("Defaults command dumps JSON-style rules")
val defaults = AutoModeRules.new(["read"], ["delete"], ["linux"])
expect(autoModeDefaultsHandler(defaults)).to_equal(writeRules(defaults))
expect(autoModeDefaultsHandler(defaults)).to_contain("\"allow\":[\"read\"]")
```

</details>

#### merges config with per-section replace semantics

- merges config with per-section replace semantics
- Non-empty user section replaces that section, empty falls back to defaults
   - Expected: merged.permit equals `["write"]`
   - Expected: merged.soft_deny equals `["delete"]`
   - Expected: merged.environment equals `["linux"]`
   - Expected: autoModeConfigHandler(Some(config), defaults) equals `writeRules(merged)`
   - Expected: autoModeConfigHandler(nil, defaults) equals `writeRules(defaults)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges config with per-section replace semantics")
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

- formats custom rules for critique
- Only non-empty custom sections are included
   - Expected: formatRulesForCritique("soft_deny", [], defaults.soft_deny) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats custom rules for critique")
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

- handles critique without custom rules
- No custom rules returns guidance and does not call side query
   - Expected: result.stdout equals `noCustomRulesMessage()`
   - Expected: result.model equals ``
   - Expected: result.querySource equals `sideQuerySource()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles critique without custom rules")
step("No custom rules returns guidance and does not call side query")
val result = autoModeCritiqueHandler(AutoModeRules.empty(), AutoModeRules.new(["read"], ["delete"], ["linux"]), "", "main", true, "")
expect(result.stdout).to_equal(noCustomRulesMessage())
expect(result.model).to_equal("")
expect(result.querySource).to_equal(sideQuerySource())
```

</details>

#### builds critique request and handles responses

- builds critique request and handles responses
- Model option is parsed, side query text is printed, empty text gets fallback
   - Expected: ok.model equals `parseUserSpecifiedModel("opus")`
   - Expected: ok.stdout equals `analyzingMessage() + "Looks good.\n"`
   - Expected: empty.stdout equals `noCritiqueGeneratedMessage()`
   - Expected: failed.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds critique request and handles responses")
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

- exports source-backed constants
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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `447d74c231891e8d783cea13464ae9deb9646ae5b8906a5330a48f7f226804d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `447d74c231891e8d783cea13464ae9deb9646ae5b8906a5330a48f7f226804d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `447d74c231891e8d783cea13464ae9deb9646ae5b8906a5330a48f7f226804d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes default rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges config with per-section replace semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/autoMode_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats custom rules for critique' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
