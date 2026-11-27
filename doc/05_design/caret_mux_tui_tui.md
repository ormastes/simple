# Caret CoreMux TUI flow and capture plan

Selected option A/N2, 2026-10-25. Requirements:
`doc/02_requirements/feature/caret_mux_tui.md` and corresponding NFR document.
Architecture/detail: `doc/04_architecture/caret_mux_tui.md` and
`doc/05_design/caret_mux_tui.md`. System plan:
`doc/03_plan/sys_test/caret_mux_tui.md`.

**NOT_RUN — design only.** Screens below describe information and actions to
capture from the production TUI; they are not screenshots or execution evidence.
No new widget hierarchy, GUI/web frontend or window manager is introduced.
Caret keeps its established Simple shared semantic UI contract; CoreMux supplies
backend ownership and terminal geometry through Sosix owners.

## Operator flow

1. Select Smux or Tmux and an isolated workspace/server namespace explicitly.
   Show actual connection outcome and backend identity. Unavailable selection
   stays unavailable; do not switch silently to the other backend.
2. Discover or create a detached session through CoreMux. The session list shows
   actual names/IDs and child status. Ambiguous targets require an unambiguous
   selection; they never resolve to whichever object appears first.
3. Open the ordinary Caret TUI in a real pane. Use existing semantic widgets to
   select sessions, windows, panes and agent conversations. Preserve argv/cwd/env
   semantics through the production child launcher.
4. Split the selected pane, focus another pane/window, select a named layout,
   resize and zoom/restore. Display only geometry acknowledged by the owner;
   do not show a local optimistic plan as committed after failure.
5. Deliver literal input, named keys, paste, commands and notifications through
   their distinct operations. Existing mandatory messaging/title/border/hide/show
   workflows remain usable even if additional optional presentation is absent.
6. Detach/close the dashboard while the independent session and child continue.
   A fresh client discovers the same owner generation/object identities and
   reconnects. Session termination is a separate deliberate action.

The following is an information arrangement, reusing current widgets rather
than specifying a new implementation:

```text
Workspace / server namespace       Selected backend and connection state
Session and window navigation      Session/pane child state
Pane area: ordinary Caret TUI      Authoritative layout and focus
Existing status / notification area
```

The status area distinguishes capability availability from execution evidence.
An advertised operation is not labeled verified merely because it was listed.
Required missing support blocks the usable-replacement claim; only genuinely
optional extension controls can be disabled with an explanatory message.

## Capture matrix

Each row runs on both real backends where the feature is mandatory. Typed
unsupported optional branches capture the refusal and unchanged state rather
than a manufactured example of successful presentation.

| Capture | Action and production observation | Independent oracle |
| --- | --- | --- |
| C01 Backend/namespace | Connect explicitly, list real detached sessions in two namespaces | CoreMux owner generation and separate native server/process identity; no namespace leakage |
| C02 Ordinary Caret pane | Launch Caret with configured cwd/env and a real child | Native PID plus child-owned argv/cwd/env report; rendered existing widgets respond to input |
| C03 Directional/nested split | Split selected pane in both axes, then split one child | Actual cell rectangles, stable IDs, independent child dimensions; unrelated panes retain topology |
| C04 Windows/clients | Select different windows in two clients and alter shared canvas | Two independent terminal captures plus owner snapshot; required client-local focus semantics remain visible |
| C05 Layout/zoom/resize | Select named layout, zoom one pane, restore and resize | Before/after rectangles and child-computed dimensions, no fabricated metadata-only zoom |
| C06 Detached continuity | Close one dashboard, then all clients; reconnect later | Owner/child survival, child-generated output while detached, same live identity on return; no request polling substituted for unattended owner progress |
| C07 Title/border/hide/show | Invoke actual audited Caret presentation workflows | Native visible change, object listing/lifecycle semantics and retained child identity |
| C08 Unicode/history | Render wide CJK, emoji, combining text, wrapped lines, styles and alternate screen | Raw transcript bytes plus cell coordinates from independent terminal observation; plain/styled and join/wrap expectations |
| C09 Input separation | Send literal newline text, named Enter, bracketed paste and a command separately | Child-observed input boundaries/mode behavior; a displayed input echo cannot satisfy command execution |
| C10 Notifications | Route an addressed notification and then acknowledge it | Native rendering success precedes ACK; queue acceptance, capture text or callback dispatch alone is insufficient |
| C11 Optional absent | Acquire or invoke absent TerminalLayoutV1/TerminalPresentationV1 | Typed Unsupported, unchanged owner revision/state and no native side effects/backend migration |
| C12 Conflict/failure | Submit stale or concurrent plans, interrupt an operation | Typed error and commit/cleanup evidence; partial state shown honestly and reconciled before retry |
| C13 Crash recovery | Kill a client without detach, then restart server separately | Recovered capacity and surviving view, old owner/object generation refused, no stale target reuse |

## Capture acquisition and artifact policy

Use the existing native terminal/console fixtures and capture helpers. Do not
replace them with prewritten ANSI output, a synthetic shell, supplied PID tables
or expected stdout files. An in-process rendered model is useful unit evidence
but cannot count as an actual independent console in C04 or native notification
rendering in C10. A screenshot alone cannot prove retained child state, cleanup
or exact UTF-8 bytes; pair it with the independent oracle in the matrix.

Capture the before state, actual action, settled observation, and any refusal.
For each capture retain SDN metadata linking backend/version, namespace/owner
generation, lease/object references, source and Phase 3/runtime/provider identity,
fixture and product hashes, action sequence, monotonic time, geometry revision,
operation commit state and artifact hashes. Bind screenshots/raw transcripts to
the real process result. Never invent or overwrite immutable historical evidence.

Tokens and credentials are excluded from screenshots/transcripts. A redacted
view must preserve the geometry/behavior under test and link to the protected
raw artifact when policy permits. Notification test content is explicit fixture
text, not a real message to another person. Clipboard writes are excluded unless
the user schedules a positive clipboard action; refusal/read-only controls must
not overwrite global clipboard contents.

Artifact buffers, transcript/history sizes and rotation counts are finite and
recorded. Use periodic snapshots and bounded event batches for the soak, not a
24-hour in-memory stdout string. Record dropped/refused evidence and capture
failures; missing evidence cannot be silently replaced by a later screenshot.

## N2 observation schedule

The baseline per backend has two namespaces, each with two sessions, at least
four panes and two clients. Larger scales are explicit configuration. Keep
screen dimensions, host/terminal versions and limits pinned for latency samples.
Measure layout completion at independently observed settled native geometry,
not at RPC acknowledgment. Metadata and layout p95 use the distributions and
thresholds in the system plan; cold preparation is reported separately.

Each backend requires a genuine continuous 24-hour background/reconnect soak.
Capture initial state, declared bounded interval snapshots, all planned
disruptions/conflicts, final live state and terminal teardown. Shorter tests may
exercise a scenario but remain incomplete soak evidence. Record real elapsed
monotonic duration, process/handle and baseline/peak/settled RSS, queue pressure,
pending cleanup and surviving owned/unowned processes.

## Executable-spec admission

The future spec path is
`test/03_system/app/llm_caret/feature/caret_mux_tui_spec.spl`. It is deliberately
absent until production interfaces/fixtures are wired. Planned helper names are
`caret_mux_setup` and `caret_mux_check_state`; primary actions use `step("...")`.
Helpers must observe the actual owner and native capture source. No no-op/fake
backend or empty scenario is an acceptable temporary implementation.

If Phase 3 lineage, real backend, matching runtime, terminal fixture or required
capability is missing, execution setup fails and the campaign records
BLOCKED/NOT_RUN. Ordinary Caret child usability on each backend remains a
mandatory core gate even when optional extension acquisition returns Unsupported.
Native execution and docgen/zero-stub checks are pending. Count all relevant
prior verification cycles toward the hard limit of six; do not restart the
budget by changing backend output paths or worktrees.
