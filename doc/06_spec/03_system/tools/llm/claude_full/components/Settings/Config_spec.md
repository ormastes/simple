# Claude Full Settings Config Slice

> Focused Simple coverage for top-level Settings Config shell behavior from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Settings Config Slice

Focused Simple coverage for top-level Settings Config shell behavior from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for top-level Settings Config shell behavior from
components/Settings/Config.tsx.

## Scenarios

### Claude full settings config parity

#### should model search and selection routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model search and selection routes
- Check settings search
   - Expected: settingsInitialRenderRoute() equals `search box footer hints`
   - Expected: settingsFilterRoute("theme", "theme", "Theme", "appearance") is true
   - Expected: settingsFilterRoute("appear", "theme", "Theme", "appearance") is true
   - Expected: settingsFilterRoute("missing", "theme", "Theme", "appearance") is false
   - Expected: settingsNoMatchRoute("missing", false) equals `No settings match "missing"`
   - Expected: settingsSearchNavigationRoute("up", 0) equals `enter search mode`
   - Expected: settingsSearchNavigationRoute("enter", 2) equals `exit search to list`
   - Expected: settingsSelectionRoute(-1, 5) equals `0`
   - Expected: settingsSelectionRoute(7, 5) equals `4`
   - Expected: settingsRowRenderRoute(true) equals `pointer highlight`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model search and selection routes")
step("Check settings search")
expect(settingsInitialRenderRoute()).to_equal("search box footer hints")
expect(settingsFilterRoute("theme", "theme", "Theme", "appearance")).to_equal(true)
expect(settingsFilterRoute("appear", "theme", "Theme", "appearance")).to_equal(true)
expect(settingsFilterRoute("missing", "theme", "Theme", "appearance")).to_equal(false)
expect(settingsNoMatchRoute("missing", false)).to_equal("No settings match \"missing\"")
expect(settingsSearchNavigationRoute("up", 0)).to_equal("enter search mode")
expect(settingsSearchNavigationRoute("enter", 2)).to_equal("exit search to list")
expect(settingsSelectionRoute(-1, 5)).to_equal(0)
expect(settingsSelectionRoute(7, 5)).to_equal(4)
expect(settingsRowRenderRoute(true)).to_equal("pointer highlight")
```

</details>

#### should model toggles submenus and close routes

- should model toggles submenus and close routes
- Check state transitions
   - Expected: settingsBooleanToggleRoute(false) is true
   - Expected: thinkingModeToggleRoute(false, true, true) equals `thinking warning`
   - Expected: thinkingModeToggleRoute(false, true, false) equals `thinking toggled`
   - Expected: settingsSubmenuRoute("Theme") equals `open submenu hide tabs`
   - Expected: settingsSubmenuRoute("Show turn duration") equals `no submenu`
   - Expected: settingsEscRoute(true) equals `revert snapshots and close`
   - Expected: settingsEscRoute(false) equals `close clean`
   - Expected: settingsAutoUpdatesRoute(true, false) equals `auto updates disabled text`
   - Expected: settingsAutoUpdatesRoute(false, true) equals `auto updates downgrade flow`
   - Expected: settingsSaveCloseRoute(2) equals `changed fields summary`
   - Expected: settingsSaveCloseRoute(0) equals `dismissed system message`
   - Expected: settingsConfigSourceLinesModeled() equals `1821`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model toggles submenus and close routes")
step("Check state transitions")
expect(settingsBooleanToggleRoute(false)).to_equal(true)
expect(thinkingModeToggleRoute(false, true, true)).to_equal("thinking warning")
expect(thinkingModeToggleRoute(false, true, false)).to_equal("thinking toggled")
expect(settingsSubmenuRoute("Theme")).to_equal("open submenu hide tabs")
expect(settingsSubmenuRoute("Show turn duration")).to_equal("no submenu")
expect(settingsEscRoute(true)).to_equal("revert snapshots and close")
expect(settingsEscRoute(false)).to_equal("close clean")
expect(settingsAutoUpdatesRoute(true, false)).to_equal("auto updates disabled text")
expect(settingsAutoUpdatesRoute(false, true)).to_equal("auto updates downgrade flow")
expect(settingsSaveCloseRoute(2)).to_equal("changed fields summary")
expect(settingsSaveCloseRoute(0)).to_equal("dismissed system message")
expect(settingsConfigSourceLinesModeled()).to_equal(1821)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `9c1bda5c76c0976ed4f1d44d2873b966c796a2589c76182c510fb55be841795a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c1bda5c76c0976ed4f1d44d2873b966c796a2589c76182c510fb55be841795a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c1bda5c76c0976ed4f1d44d2873b966c796a2589c76182c510fb55be841795a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/Settings/Config_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/Settings/Config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/Settings/Config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model search and selection routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model search and selection routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model toggles submenus and close routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/Settings/Config_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model toggles submenus and close routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
