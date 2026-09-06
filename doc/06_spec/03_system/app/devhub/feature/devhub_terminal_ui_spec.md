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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This process-boundary specification launches the production `bin/devhub`
wrapper. It proves that the wrapper rejects identity-only bootstrap compilers,
reaches the DevHub entrypoint, accepts the shared TUI surface prefix, and
preserves CLI exit behavior. No backend credentials or network access are used.

**TUI Captures:** build/test-artifacts/03_system/app/devhub/feature/devhub_terminal_ui/help_tui.txt
**Screenshots:** doc/06_spec/image/03_system/app/devhub/feature/devhub_terminal_ui/devhub_gui.png

## User outcome

A developer can invoke `bin/devhub` from a terminal and see DevHub, rather than
an error from whichever compiler artifact happens to be first in the wrapper's
candidate list. The same entrypoint accepts the shared `--tui` prefix and
renders a reviewable help surface.

## Failure reproduced before the fix

The production wrapper considered a runtime usable when `--version` returned
zero. The deployed bootstrap compiler satisfies that identity probe but does
not implement the `run` command. Consequently `bin/devhub --help` exited one
with `error: unknown command 'run'` before loading `src/app/devhub/main.spl`.

## Runtime selection contract

The launcher must select an executable whose help advertises the deployed
`simple test` command. This capability witness rejects the identity-only
bootstrap while admitting the full self-hosted CLI used to execute DevHub.
An explicit `SIMPLE_BINARY` override is subject to the same capability check;
an executable filename alone is insufficient.

## Scope

The scenarios cover:

- production wrapper runtime selection;
- real DevHub source-entrypoint dispatch;
- terminal help visibility;
- shared TUI output-surface argument parsing;
- application version identity;
- unknown-command exit status and diagnostic;
- durable TUI transcript capture;
- Fluid OS light-liquid theme identity and six visible GUI facade cards;
- Electron-default/browser-override GUI launch parsing and port safety.

## Exclusions

The scenarios deliberately do not contact Jira, GitHub, Bitbucket,
Confluence, MinIO, Outlook, Gmail, or another mail server. They do not validate
credentials, remote API compatibility, network latency, terminal pixels, ANSI
color policy, or interactive keyboard input. Backend behavior remains covered
by offline unit fixtures and separately authorized live checks.

## Process matrix

| Invocation | Expected exit | Required visible evidence |
|---|---:|---|
| `bin/devhub --help` | 0 | DevHub title, usage, and TUI option |
| `bin/devhub --tui --help` | 0 | DevHub title and surface choices |
| `bin/devhub --version` | 0 | exact `devhub 0.1.0` identity |
| `bin/devhub not-a-devhub-command` | 1 | unknown command names the input |
| `bin/devhub --gui` | long-running | loopback server plus Electron Fluid OS window |

## Modern SSpec flow

Every scenario uses `step("...")` labels that describe operator actions and
checks. Assertions use only canonical matchers. The TUI scenario records the
actual stdout transcript under `build/test-artifacts` so the generated manual
can embed what a terminal user sees.

## Syntax

Run the focused interpreter system test:

```bash
bin/simple test --no-session-daemon test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl --mode=interpreter
```

Regenerate this manual:

```bash
bin/simple spipe-docgen test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl --output doc/06_spec --no-index
```

Exercise the terminal directly:

```bash
bin/devhub --help
bin/devhub --tui --help
bin/devhub --version
```

## Discovery diagnosis

Before this specification existed, asking the SSpec runner for
`test/03_system/app/devhub` returned `No test files found` and `0 indexed`.
That result was not a hidden parser failure: the directory contained no system
specification at all, while the existing DevHub coverage lived entirely under
`test/01_unit/app/devhub`. This file supplies the missing process-boundary lane
at the canonical system-test path.

## Failure handling

If help shows compiler usage or reports an unknown `run` command, inspect the
runtime selected by `bin/devhub` and confirm its help contains the full CLI
surface. If the TUI scenario fails after normal help passes, inspect global
prefix parsing in `_itf_global_log_args` and `_itf_clean_global_log_args`. If
version output contains a compiler identity, confirm dispatch reached
`handle_itf` in the DevHub entrypoint.

## Pass criteria

The runner must discover one spec with ten examples. All ten examples must
pass, the process exits must match the matrix, and the TUI capture must be
written and read back byte-for-byte. A zero-example result, a bootstrap
identity response, or a static source-only assertion is not acceptance.

## Evidence boundary

A pass proves local production-wrapper selection and DevHub terminal dispatch
on this checkout. It does not prove remote backend availability or graphical
terminal rendering. The captured help transcript is visible-state evidence;
the process exit and application-specific text prove that the real entrypoint
handled the request.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DEVHUB-TERM-001
```

</details>

#### should launch with the shared TUI output surface

- should launch with the shared TUI output surface
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
# @req REQ-SSPEC-SYSTEM
step("should launch with the shared TUI output surface")
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

- should print the application version rather than compiler identity
- Request the DevHub version through the production wrapper
- Check the exact application identity
   - Expected: exit_code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: stdout.trim() equals `devhub 0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should print the application version rather than compiler identity")
step("Request the DevHub version through the production wrapper")
val (stdout, stderr, exit_code) = run_devhub(["--version"])

step("Check the exact application identity")
expect(exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(stdout.trim()).to_equal("devhub 0.1.0")
```

</details>

#### should return failure for an unknown command

- should return failure for an unknown command
- Submit an unknown DevHub command
- Check the failure exit and actionable command name
   - Expected: exit_code equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return failure for an unknown command")
step("Submit an unknown DevHub command")
val (stdout, stderr, exit_code) = run_devhub(["not-a-devhub-command"])

step("Check the failure exit and actionable command name")
expect(exit_code).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(stdout).to_contain("Unknown command: not-a-devhub-command")
```

</details>

#### should expose the six DevHub facades in the GUI document

- should expose the six DevHub facades in the GUI document
- Build the production DevHub GUI document
- Check the visible dashboard identity and facade cards
- Check the loopback GUI readiness contract
   - Expected: devhub_gui_status_json() equals `{"app":"devhub","status":"ready","surface":"gui","commands":6}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the six DevHub facades in the GUI document")
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

- should expose clickable facade buttons and visible post-click state
- Build the interactive DevHub GUI document
- Check semantic button and keyboard-accessible selection contracts
- Check the visible action panel and click delivery handlers


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose clickable facade buttons and visible post-click state")
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

- should select Electron by default and allow an explicit browser shell
- Parse the default GUI launch options
   - Expected: default_options.0 equals `8765`
   - Expected: default_options.1 equals `electron`
- Select a browser shell and an alternate loopback port
   - Expected: browser_options.0 equals `9876`
   - Expected: browser_options.1 equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select Electron by default and allow an explicit browser shell")
step("Parse the default GUI launch options")
val default_options = devhub_gui_options([])
expect(default_options.0).to_equal(8765)
expect(default_options.1).to_equal("electron")

step("Select a browser shell and an alternate loopback port")
val browser_options = devhub_gui_options(["--browser", "--port", "9876"])
expect(browser_options.0).to_equal(9876)
expect(browser_options.1).to_equal("browser")
```

</details>

#### should launch the resolved Electron application instead of its welcome screen

- Resolve the managed Electron package and build the launch arguments
- Require a real package manifest and an explicit application path

The managed package directory is passed explicitly before `--url`. A missing
manifest or executable fails closed, so Electron's default welcome screen
cannot count as a successful DevHub render.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-DEVHUB-TERM-001
step("Resolve the managed Electron package and build the launch arguments")
val launch = resolve_electron_app_launch(".")
val args = electron_app_launch_args(launch.package_dir,
    "http://127.0.0.1:8765/", "")
expect(launch.ready).to_be(true)
expect(args[1]).to_equal(launch.package_dir)
expect(args[2]).to_equal("--url")
```

</details>

#### should reject an unsafe GUI port before opening a window

- should reject an unsafe GUI port before opening a window
- Launch the production wrapper with a privileged GUI port
- Check the fail-closed port diagnostic
   - Expected: exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unsafe GUI port before opening a window")
step("Launch the production wrapper with a privileged GUI port")
val (stdout, stderr, exit_code) = run_devhub(["--gui", "--port", "80"])

step("Check the fail-closed port diagnostic")
expect(exit_code).to_equal(2)
expect(stdout).to_contain("--port must be between 1024 and 65535")
```

</details>

#### should hide successful launch diagnostics by default and expose them on request

- should hide successful launch diagnostics by default and expose them on request
- Launch a successful CLI command with the default clean output
   - Expected: quiet_exit equals `0`
   - Expected: quiet_stdout.trim() equals `devhub 0.1.0`
   - Expected: quiet_stderr.trim() equals ``
- Enable verbose compiler and launch diagnostics
   - Expected: verbose_exit equals `0`
   - Expected: verbose_stdout.trim() equals `devhub 0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should hide successful launch diagnostics by default and expose them on request")
step("Launch a successful CLI command with the default clean output")
val (quiet_stdout, quiet_stderr, quiet_exit) = run_devhub(["--version"])
expect(quiet_exit).to_equal(0)
expect(quiet_stdout.trim()).to_equal("devhub 0.1.0")
expect(quiet_stderr.trim()).to_equal("")

step("Enable verbose compiler and launch diagnostics")
val (verbose_stdout, verbose_stderr, verbose_exit) = run_devhub(["--verbose", "--version"])
expect(verbose_exit).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-DEVHUB-TERM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17cb3ed7532dd8e4ac85118875da0f52cbfb66624e384670c794b985221c1218`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17cb3ed7532dd8e4ac85118875da0f52cbfb66624e384670c794b985221c1218`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17cb3ed7532dd8e4ac85118875da0f52cbfb66624e384670c794b985221c1218`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **80/100**; blockers: **0**.

SSpec documentization score: 80/100
source: test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl
mirror: doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md (current)
findings: 13 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:169:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should print DevHub help through the production wrapper' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:169:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should print DevHub help through the production wrapper' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:184:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should launch with the shared TUI output surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:198:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should print the application version rather than compiler identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should print the application version rather than compiler identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:208:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return failure for an unknown command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return failure for an unknown command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the six DevHub facades in the GUI document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the six DevHub facades in the GUI document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl:240:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose clickable facade buttons and visible post-click state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
