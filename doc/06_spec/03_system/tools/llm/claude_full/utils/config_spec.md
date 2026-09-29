# Claude Full Config Slice

> Focused coverage for pure config selectors and predicates from utils/config.ts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Config Slice

Focused coverage for pure config selectors and predicates from utils/config.ts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for pure config selectors and predicates from utils/config.ts.

## Scenarios

### Claude full config parity

#### should model default config and key allowlists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model default config and key allowlists
- Check key predicates
   - Expected: defaultGlobalConfigRoute() equals `empty arrays maps false onboarding trust`
   - Expected: isGlobalConfigKey("theme") is true
   - Expected: isGlobalConfigKey("unknown") is false
   - Expected: isProjectConfigKey("allowedTools") is true
   - Expected: isProjectConfigKey("unknown") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model default config and key allowlists")
step("Check key predicates")
expect(defaultGlobalConfigRoute()).to_equal("empty arrays maps false onboarding trust")
expect(isGlobalConfigKey("theme")).to_equal(true)
expect(isGlobalConfigKey("unknown")).to_equal(false)
expect(isProjectConfigKey("allowedTools")).to_equal(true)
expect(isProjectConfigKey("unknown")).to_equal(false)
```

</details>

#### should model status remote control and updater reasons

- should model status remote control and updater reasons
- Check selectors
   - Expected: getCustomApiKeyStatusRoute(true, true, true) equals `approved`
   - Expected: getCustomApiKeyStatusRoute(false, true, true) equals `rejected`
   - Expected: getCustomApiKeyStatusRoute(false, false, false) equals `new`
   - Expected: getRemoteControlAtStartupRoute(true, true) is true
   - Expected: getRemoteControlAtStartupRoute(false, true) is false
   - Expected: formatAutoUpdaterDisabledReasonRoute("development") equals `Auto-updates are disabled in development builds.`
   - Expected: formatAutoUpdaterDisabledReasonRoute("env") equals `Auto-updates are disabled by environment.`
   - Expected: formatAutoUpdaterDisabledReasonRoute("config") equals `Auto-updates are disabled in configuration.`
   - Expected: getAutoUpdaterDisabledReasonRoute(true, true, true, true) equals `development`
   - Expected: getAutoUpdaterDisabledReasonRoute(false, true, true, true) equals `env`
   - Expected: getAutoUpdaterDisabledReasonRoute(false, false, true, true) equals `essential_traffic_env`
   - Expected: getAutoUpdaterDisabledReasonRoute(false, false, false, true) equals `config`
   - Expected: getAutoUpdaterDisabledReasonRoute(false, false, false, false) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model status remote control and updater reasons")
step("Check selectors")
expect(getCustomApiKeyStatusRoute(true, true, true)).to_equal("approved")
expect(getCustomApiKeyStatusRoute(false, true, true)).to_equal("rejected")
expect(getCustomApiKeyStatusRoute(false, false, false)).to_equal("new")
expect(getRemoteControlAtStartupRoute(true, true)).to_equal(true)
expect(getRemoteControlAtStartupRoute(false, true)).to_equal(false)
expect(formatAutoUpdaterDisabledReasonRoute("development")).to_equal("Auto-updates are disabled in development builds.")
expect(formatAutoUpdaterDisabledReasonRoute("env")).to_equal("Auto-updates are disabled by environment.")
expect(formatAutoUpdaterDisabledReasonRoute("config")).to_equal("Auto-updates are disabled in configuration.")
expect(getAutoUpdaterDisabledReasonRoute(true, true, true, true)).to_equal("development")
expect(getAutoUpdaterDisabledReasonRoute(false, true, true, true)).to_equal("env")
expect(getAutoUpdaterDisabledReasonRoute(false, false, true, true)).to_equal("essential_traffic_env")
expect(getAutoUpdaterDisabledReasonRoute(false, false, false, true)).to_equal("config")
expect(getAutoUpdaterDisabledReasonRoute(false, false, false, false)).to_equal("none")
```

</details>

#### should model memory and rules paths

- should model memory and rules paths
- Check path selectors
   - Expected: getMemoryPathRoute("User", "/cfg", "/repo", false) equals `/cfg/CLAUDE.md`
   - Expected: getMemoryPathRoute("Local", "/cfg", "/repo", false) equals `/repo/CLAUDE.local.md`
   - Expected: getMemoryPathRoute("Project", "/cfg", "/repo", false) equals `/repo/CLAUDE.md`
   - Expected: getMemoryPathRoute("Managed", "/cfg", "/repo", false) equals `/cfg/managed/CLAUDE.md`
   - Expected: getMemoryPathRoute("AutoMem", "/cfg", "/repo", false) equals `/cfg/automem/CLAUDE.md`
   - Expected: getMemoryPathRoute("TeamMem", "/cfg", "/repo", true) equals `/cfg/automem/team/MEMORY.md`
   - Expected: getMemoryPathRoute("TeamMem", "/cfg", "/repo", false) equals ``
   - Expected: getManagedClaudeRulesDirRoute("/cfg") equals `/cfg/managed`
   - Expected: getUserClaudeRulesDirRoute("/cfg") equals `/cfg/rules`
   - Expected: claudeConfigSourceLinesModeled() equals `1817`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model memory and rules paths")
step("Check path selectors")
expect(getMemoryPathRoute("User", "/cfg", "/repo", false)).to_equal("/cfg/CLAUDE.md")
expect(getMemoryPathRoute("Local", "/cfg", "/repo", false)).to_equal("/repo/CLAUDE.local.md")
expect(getMemoryPathRoute("Project", "/cfg", "/repo", false)).to_equal("/repo/CLAUDE.md")
expect(getMemoryPathRoute("Managed", "/cfg", "/repo", false)).to_equal("/cfg/managed/CLAUDE.md")
expect(getMemoryPathRoute("AutoMem", "/cfg", "/repo", false)).to_equal("/cfg/automem/CLAUDE.md")
expect(getMemoryPathRoute("TeamMem", "/cfg", "/repo", true)).to_equal("/cfg/automem/team/MEMORY.md")
expect(getMemoryPathRoute("TeamMem", "/cfg", "/repo", false)).to_equal("")
expect(getManagedClaudeRulesDirRoute("/cfg")).to_equal("/cfg/managed")
expect(getUserClaudeRulesDirRoute("/cfg")).to_equal("/cfg/rules")
expect(claudeConfigSourceLinesModeled()).to_equal(1817)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `586ed97fb84d07b6089cde59ddcadb96d1395cbeba64c54e51c998b2d59a9c53`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `586ed97fb84d07b6089cde59ddcadb96d1395cbeba64c54e51c998b2d59a9c53`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `586ed97fb84d07b6089cde59ddcadb96d1395cbeba64c54e51c998b2d59a9c53`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/config_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/config_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model default config and key allowlists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model default config and key allowlists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model status remote control and updater reasons' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model status remote control and updater reasons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model memory and rules paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/config_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model memory and rules paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
