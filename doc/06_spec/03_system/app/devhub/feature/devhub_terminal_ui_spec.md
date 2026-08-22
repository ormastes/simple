# DevHub terminal and UI-surface launch

> Verifies the devhub terminal ui behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DevHub terminal and UI-surface launch

Verifies the devhub terminal ui behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/devhub_terminal_ui.md |
| Design | doc/05_design/app/devhub/devhub_overview.md |
| Research | N/A |
| Source | `test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the devhub terminal ui behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Screenshots | 1 |
| TUI Captures | 1 |

### Screenshots

| Item | Kind | Path |
|------|------|------|
| `devhub_gui.png` | Screenshot | `doc/06_spec/image/03_system/app/devhub/feature/devhub_terminal_ui/devhub_gui.png` |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `help_tui.txt` | TUI capture | `build/test-artifacts/03_system/app/devhub/feature/devhub_terminal_ui/help_tui.txt` |

## Scenarios

### REQ-DEVHUB-TERM-001: launch the real DevHub app on terminal and TUI surfaces

#### should print DevHub help through the production wrapper

- Verify: should print DevHub help through the production wrapper
- Launch DevHub on the terminal
- Check that application help, not compiler help, is visible
   - Expected: exit_code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: stderr.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should print DevHub help through the production wrapper")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Launch DevHub on the terminal")
val (stdout, stderr, exit_code) = run_devhub(["--help"])

step("Check that application help, not compiler help, is visible")
expect(exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(stdout).to_contain("devhub — famous-CLI ergonomics")
expect(stdout).to_contain("Usage: devhub <command> [flags]")
expect(stdout).to_contain("--tui")
expect(stderr.trim()).to_equal("")
```

</details>

#### should launch with the shared TUI output surface

- Verify: should launch with the shared TUI output surface
- Launch DevHub with the TUI surface prefix
- Check the visible DevHub TUI help surface
   - Expected: exit_code equals `0)  # oracle: pinned constant asserted by this scenario`
- Capture the TUI surface for the generated manual
   - Expected: capture_tui_help(stdout) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should launch with the shared TUI output surface")
step("Launch DevHub with the TUI surface prefix")
val (stdout, stderr, exit_code) = run_devhub(["--tui", "--help"])

step("Check the visible DevHub TUI help surface")
expect(exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(stdout).to_contain("devhub — famous-CLI ergonomics")
expect(stdout).to_contain("--stdout | --tui")

step("Capture the TUI surface for the generated manual")
expect(capture_tui_help(stdout)).to_equal(true)
```

</details>

#### should print the application version rather than compiler identity

- Verify: should print the application version rather than compiler identity
- Request the DevHub version through the production wrapper
- Check the exact application identity
   - Expected: exit_code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: stdout.trim() equals `devhub 0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should print the application version rather than compiler identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Request the DevHub version through the production wrapper")
val (stdout, stderr, exit_code) = run_devhub(["--version"])

step("Check the exact application identity")
expect(exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(stdout.trim()).to_equal("devhub 0.1.0")
```

</details>

#### should return failure for an unknown command

- Verify: should return failure for an unknown command
- Submit an unknown DevHub command
- Check the failure exit and actionable command name
   - Expected: exit_code equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should return failure for an unknown command")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Submit an unknown DevHub command")
val (stdout, stderr, exit_code) = run_devhub(["not-a-devhub-command"])

step("Check the failure exit and actionable command name")
expect(exit_code).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(stdout).to_contain("Unknown command: not-a-devhub-command")
```

</details>

#### should expose the six DevHub facades in the GUI document

- Verify: should expose the six DevHub facades in the GUI document
- Build the production DevHub GUI document
- Check the visible dashboard identity and facade cards
- Check the loopback GUI readiness contract
   - Expected: devhub_gui_status_json() equals `{"app":"devhub","status":"ready","surface":"gui","commands":6}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should expose the six DevHub facades in the GUI document")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the production DevHub GUI document")
val html = devhub_gui_html()

step("Check the visible dashboard identity and facade cards")
expect(html).to_contain("DevHub developer tools dashboard")
expect(html).to_contain("Local GUI connected")
expect(html).to_contain("--app-background-image")
expect(html).to_contain("--glass-surface: rgba(255,255,255,0.72)")
expect(html).to_contain("color-scheme: light")
expect(html).to_contain(">Tasks<")
expect(html).to_contain(">GitHub<")
expect(html).to_contain(">Bitbucket<")
expect(html).to_contain(">Wiki<")
expect(html).to_contain(">Storage<")
expect(html).to_contain(">Email<")

step("Check the loopback GUI readiness contract")
expect(devhub_gui_status_json()).to_equal("{\"app\":\"devhub\",\"status\":\"ready\",\"surface\":\"gui\",\"commands\":6}")
```

</details>

#### should expose clickable facade buttons and visible post-click state

- Verify: should expose clickable facade buttons and visible post-click state
- Build the interactive DevHub GUI document
- Check semantic button and keyboard-accessible selection contracts
- Check the visible action panel and click delivery handlers


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should expose clickable facade buttons and visible post-click state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the interactive DevHub GUI document")
val html = devhub_gui_html()

step("Check semantic button and keyboard-accessible selection contracts")
expect(html).to_contain("<button type=\"button\" class=\"card\"")
expect(html).to_contain("aria-controls=\"command-detail\"")
expect(html).to_contain("aria-pressed=\"false\"")
expect(html).to_contain("class=\"open-label\">Open →")

step("Check the visible action panel and click delivery handlers")
expect(html).to_contain("id=\"command-detail\"")
expect(html).to_contain("id=\"copy-command\"")
expect(html).to_contain("card.addEventListener('click'")
expect(html).to_contain("statusNode.textContent = card.dataset.name + ' selected'")
expect(html).to_contain("navigator.clipboard.writeText(command)")
```

</details>

#### should select Electron by default and allow an explicit browser shell

- Verify: should select Electron by default and allow an explicit browser shell
- Parse the default GUI launch options
   - Expected: default_options.0 equals `8765)  # oracle: pinned constant asserted by this scenario`
   - Expected: default_options.1 equals `electron`
- Select a browser shell and an alternate loopback port
   - Expected: browser_options.0 equals `9876)  # oracle: pinned constant asserted by this scenario`
   - Expected: browser_options.1 equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should select Electron by default and allow an explicit browser shell")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Parse the default GUI launch options")
val default_options = devhub_gui_options([])
expect(default_options.0).to_equal(8765)  # oracle: pinned constant asserted by this scenario
expect(default_options.1).to_equal("electron")

step("Select a browser shell and an alternate loopback port")
val browser_options = devhub_gui_options(["--browser", "--port", "9876"])
expect(browser_options.0).to_equal(9876)  # oracle: pinned constant asserted by this scenario
expect(browser_options.1).to_equal("browser")
```

</details>

#### should reject an unsafe GUI port before opening a window

- Verify: should reject an unsafe GUI port before opening a window
- Launch the production wrapper with a privileged GUI port
- Check the fail-closed port diagnostic
   - Expected: exit_code equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should reject an unsafe GUI port before opening a window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Launch the production wrapper with a privileged GUI port")
val (stdout, stderr, exit_code) = run_devhub(["--gui", "--port", "80"])

step("Check the fail-closed port diagnostic")
expect(exit_code).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(stdout).to_contain("--port must be between 1024 and 65535")
```

</details>

#### should hide successful launch diagnostics by default and expose them on request

- Verify: should hide successful launch diagnostics by default and expose them on request
- Launch a successful CLI command with the default clean output
   - Expected: quiet_exit equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: quiet_stdout.trim() equals `devhub 0.1.0`
   - Expected: quiet_stderr.trim() equals ``
- Enable verbose compiler and launch diagnostics
   - Expected: verbose_exit equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: verbose_stdout.trim() equals `devhub 0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DEVHUB-TERM-001
step("Verify: should hide successful launch diagnostics by default and expose them on request")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Launch a successful CLI command with the default clean output")
val (quiet_stdout, quiet_stderr, quiet_exit) = run_devhub(["--version"])
expect(quiet_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(quiet_stdout.trim()).to_equal("devhub 0.1.0")
expect(quiet_stderr.trim()).to_equal("")

step("Enable verbose compiler and launch diagnostics")
val (verbose_stdout, verbose_stderr, verbose_exit) = run_devhub(["--verbose", "--version"])
expect(verbose_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(verbose_stdout.trim()).to_equal("devhub 0.1.0")
expect(verbose_stderr).to_contain("warning")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/devhub_terminal_ui.md`
- **Design:** `doc/05_design/app/devhub/devhub_overview.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58f1fd03f87753a04ae0f86363680eda6f7b6ba34b410ff5ec49d335f1304e30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58f1fd03f87753a04ae0f86363680eda6f7b6ba34b410ff5ec49d335f1304e30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58f1fd03f87753a04ae0f86363680eda6f7b6ba34b410ff5ec49d335f1304e30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl
mirror: doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:179:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should print DevHub help through the production wrapper' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:193:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should launch with the shared TUI output surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:207:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should print the application version rather than compiler identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return failure for an unknown command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:229:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the six DevHub facades in the GUI document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:252:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose clickable facade buttons and visible post-click state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
