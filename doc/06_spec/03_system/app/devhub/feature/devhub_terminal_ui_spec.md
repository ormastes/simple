# DevHub terminal and UI-surface launch

> This process-boundary specification launches the production `bin/devhub` wrapper. It proves that the wrapper rejects identity-only bootstrap compilers, reaches the DevHub entrypoint, accepts the shared TUI surface prefix, and preserves CLI exit behavior. No backend credentials or network access are used.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DevHub terminal and UI-surface launch

This process-boundary specification launches the production `bin/devhub` wrapper. It proves that the wrapper rejects identity-only bootstrap compilers, reaches the DevHub entrypoint, accepts the shared TUI surface prefix, and preserves CLI exit behavior. No backend credentials or network access are used.

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
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This process-boundary specification launches the production `bin/devhub`
wrapper. It proves that the wrapper rejects identity-only bootstrap compilers,
reaches the DevHub entrypoint, accepts the shared TUI surface prefix, and
preserves CLI exit behavior. No backend credentials or network access are used.

**TUI Captures:** build/test-artifacts/03_system/app/devhub/feature/devhub_terminal_ui/help_tui.txt

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
- durable TUI transcript capture.

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

The runner must discover one spec with nine examples. All nine examples must
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
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `help_tui.txt` | TUI capture | `build/test-artifacts/03_system/app/devhub/feature/devhub_terminal_ui/help_tui.txt` |

#### Embedded TUI Text Captures

<details>
<summary>help_tui.txt</summary>

```text
usage: 0/1 (0%)
devhub — famous-CLI ergonomics over your configured backends

Usage: devhub <command> [flags]

Facades (one UX, several backends — pick with --backend):
  tasks, task_manager  gh-issue UX over Jira + GitHub (list, view, create, edit, close)
  github, gh           gh UX over GitHub (issue, pr, repo) via the system gh CLI
  bb, b                gh-shaped UX over Bitbucket Cloud (pr, comment, approve, merge)
  wiki, w              gh-like UX over Confluence + GitHub wiki (list, view, edit, create)
  storage, web_storage mc UX over MinIO/S3 (ls, cp, cat, stat, mirror, presign, rm, mb)
  email                Gmail UX over Gmail/IMAP + MS Graph (inbox, read, search, send)

Direct backend commands:
  jira, j           Jira issues (view, search, create)
  minio, mio        MinIO/S3 (ls, get, put, stat, presign, health)
  outlook, ol       Microsoft Graph mail (folders, messages, get, move, mark)
  api               Raw REST API calls
  auth              Authentication (login, status, logout)
  daily-debug, dd   Daily debug-analysis pipeline (mail → jira → minio → triage)

Flags:
  --json       Output as JSON (with optional field selection)
  --jq EXPR    Filter JSON output (e.g. .[].title)
  --web        Open in browser
  --no-pager   Never page long listing output (jira search, github list, minio ls)
  --help, -h   Show help
  --version    Show version

Examples:
  devhub auth login --confluence --url https://company.atlassian.net/wiki --user email --token TOKEN
  devhub tasks list --backend jira --assignee @me --state open
  devhub tasks create --title "fix login" --body "steps..."
  devhub storage ls myminio/backups --bytes
  devhub storage mirror ./dist myminio/site --dry-run
  devhub email search "from:alerts is:unread" --limit 20
  devhub wiki list --space ENG
  devhub jira search "project = PROJ" --limit 10

Environment:
  ITF_EDITOR       Editor override
  ITF_PAGER        Pager override
  ITF_FORCE_COLOR  Force color output (1/0)
  NO_COLOR         Disable color output

Config: ~/.config/itf/config.sdn

Shared log options:
  --log-mode <human|llm|json>  Select log rendering mode
  --human | --llm | --json     Shorthand log modes
  --stdout | --tui             Select output surface
  --progress <summary|count|dot|none>
  --dots | --count | --no-progress
  --quiet | --verbose
```

</details>

## Scenarios

### REQ-DEVHUB-TERM-001: launch the real DevHub app on terminal and TUI surfaces

#### should print DevHub help through the production wrapper

- Launch DevHub on the terminal
- Check that application help, not compiler help, is visible
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch DevHub on the terminal")
val (stdout, stderr, exit_code) = run_devhub(["--help"])

step("Check that application help, not compiler help, is visible")
expect(exit_code).to_equal(0)
expect(stdout).to_contain("devhub — famous-CLI ergonomics")
expect(stdout).to_contain("Usage: devhub <command> [flags]")
expect(stdout).to_contain("--tui")
```

</details>

#### should launch with the shared TUI output surface

- Launch DevHub with the TUI surface prefix
- Check the visible DevHub TUI help surface
   - Expected: exit_code equals `0`
- Capture the TUI surface for the generated manual
   - Expected: capture_tui_help(stdout) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch DevHub with the TUI surface prefix")
val (stdout, stderr, exit_code) = run_devhub(["--tui", "--help"])

step("Check the visible DevHub TUI help surface")
expect(exit_code).to_equal(0)
expect(stdout).to_contain("devhub — famous-CLI ergonomics")
expect(stdout).to_contain("--stdout | --tui")

step("Capture the TUI surface for the generated manual")
expect(capture_tui_help(stdout)).to_equal(true)
```

</details>

#### should print the application version rather than compiler identity

- Request the DevHub version through the production wrapper
- Check the exact application identity
   - Expected: exit_code equals `0`
   - Expected: stdout.trim() equals `devhub 0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request the DevHub version through the production wrapper")
val (stdout, stderr, exit_code) = run_devhub(["--version"])

step("Check the exact application identity")
expect(exit_code).to_equal(0)
expect(stdout.trim()).to_equal("devhub 0.1.0")
```

</details>

#### should return failure for an unknown command

- Submit an unknown DevHub command
- Check the failure exit and actionable command name
   - Expected: exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit an unknown DevHub command")
val (stdout, stderr, exit_code) = run_devhub(["not-a-devhub-command"])

step("Check the failure exit and actionable command name")
expect(exit_code).to_equal(1)
expect(stdout).to_contain("Unknown command: not-a-devhub-command")
```

</details>

## Scenario Summary

In addition to the four terminal scenarios reproduced above, the executable
spec verifies the Fluid-light GUI document, semantic clickable facade buttons,
Electron/browser shell selection, unsafe-port rejection, and clean-by-default
diagnostics with explicit `--verbose` opt-in.

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
