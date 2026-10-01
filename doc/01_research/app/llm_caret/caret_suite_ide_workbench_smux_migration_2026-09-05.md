# Caret Suite: IDE Workbench Migration, smux Integration, and TUI/GUI Hardening

**Date:** 2026-09-05
**Repository inspected:** `ormastes/simple`
**Source revision:** `ea4fb1eb3d7e0b83db136d958e3d25dd667236a7`
**Status:** Research, source-level assessment, proposed design, and parallel implementation plan. No repository changes, builds, live-provider tests, or performance measurements were performed for this report.

## 1. Executive decision

Make **Caret a profile and plugin family of the shared Simple IDE workbench**, rather than building another independent dashboard. Add **smux as the IDE's general terminal service**, reusable by editors, agent sessions, builds, tests, debuggers, and ordinary shells. Keep the existing Caret provider implementations and launch surfaces behind compatibility adapters.

The default Caret workspace must preserve the requested composition: **left: agent roster, selected-agent details, and message/command composer; right: one large selected session and a strip of smaller inactive sessions**. This is the primary product layout, not an optional dashboard hidden behind an editor-first screen.

The key architectural separations are:

| Separation | Decision |
|---|---|
| Product presentation versus execution | TUI and GUI observe the same session host. Switching views does not spawn, stop, or duplicate agents. |
| Native CLI fidelity versus structured conversations | Support terminal-backed Codex/Claude sessions and structured session views. Do not pretend a transcript renderer is the original provider TUI. |
| Terminal ownership versus process ownership | smux owns terminal identity, screen state, attachments, and layout. The execution service owns actual process/PTY lifecycle and cancellation. |
| Model engine versus agent | Slang supplies inference; Caret supplies the session, tools, policy, and user-facing agent loop. |
| Framework reuse versus eager loading | Reuse the IDE's workbench, commands, focus, docking, settings, themes, and editor services without loading every IDE application into Caret. |

**Delivery order:** repair truthful lifecycle and terminal contracts; make the shared IDE launch persistent; integrate live smux; migrate the TUI; migrate the GUI; then graduate individual structured provider integrations and recovery capabilities through real acceptance gates.

## 2. Evidence boundaries and current source assessment

The following findings describe the inspected revision, not an exhaustive repository audit. A source-level defect is not labeled as a reproduced runtime failure. Historical repository reports are evidence of what those reports recorded, not independent test results from this work.

### 2.1 What exists and what must change

| Area | Inspected evidence | Interpretation and migration action |
|---|---|---|
| Simple IDE entry | `src/app/ide/main.spl` parses shared launch options, handles feature reports, then prints a readiness message and returns. [R1] | `--tui` and `--gui` need a real persistent workbench path. Preserve explicit readiness/help behavior for automation. |
| Existing interactive editor | `src/app/editor/main.spl` calls `editor_tui_run`, `gui_shell_run`, or `gui_shell_run_sdl` for explicit interactive flags. [R2] | Reuse these launch paths and extract shared orchestration; do not start a new GUI framework. |
| Existing GUI shell | `gui_shell.spl` uses `EditorController`, extension activation, mouse/docking handling, rendering, and event polling. The shown initialization activates `*`, Simple, and Markdown. [R3] | Retain services but introduce profile-specific activation and dirty/event-driven updates. Its unconditional render call per loop is a performance investigation target, not proof of a busy loop without inspecting backend wait behavior. |
| IDE terminal panel | `src/lib/editor/view/terminal_panel.spl` is a line array, input string, and text renderer. [R4] | It is not, by itself, an interactive PTY emulator. Replace its backing model with the shared terminal service while preserving public compatibility where practical. |
| IDE plugin metadata | `plugin_manifest.spl` uses the existing `app.plugin.registry` format. Feature reporting also has a separate capability-truth report. [R5][R6] | Reuse the existing manifest and capability-reporting machinery; avoid another plugin format. Extend actual activation checks instead of equating metadata with working UI. |
| Caret entry | Supports TUI/plain/browser GUI/Electron-related modes and provider routing, including `slang` and `slang_local`. [R7] | Preserve these entry points while routing interactive workbench modes through shared IDE services. Keep prompt-only/server paths startup-light. |
| Caret browser GUI | A centered single-conversation page with one-line input and a fetch-based request; the initial status text is statically `Connected`. Its shown native HTML helper uses fixed dimensions. [R8] | Replace the product composition with the workbench. Preserve safe text rendering. Add real connection status, streaming, cancellation, responsive layout, and per-session drafts. |
| Caret manager | Bounded team launch, rollback, stop, and roster derivation exist; the embedded terminal view explicitly does not claim integration with the separate smux service. [R9] | Retain the process adapter and provide a real mux attachment adapter. |
| Native smux API | Session/window/pane operations exist. In the inspected API, send feeds a buffer, focus calls return success without setting focus, startup time is `1u64`, and a missing capture produces an artificial one-row result. [R10] | These paths cannot establish real terminal or performance acceptance. Correct semantics before using them as UI truth. |
| smux capacity | `ServiceState` declares eight session/window/pane slots and four attachments, while the Caret manager accepts capacity up to sixteen. [R11][R9] | Negotiate and reserve actual capacities across services before launch. Never admit a sixteen-agent team into an eight-pane backend without a clear refusal or an implemented larger pool. |
| Slang progress | A September 4 repository record reports real in-process GGUF inference via ggml and `slang_local`, while deliberately leaving the broader gate non-passing. HTTP lifecycle and native-pack execution remain separately unaccepted. [R12] | Do not repeat the earlier “local Slang inference is missing” conclusion. Display transport, execution backend, and readiness separately. |

### 2.2 Immediate defect candidates and regression tests

| ID | Source-level observation | Required test before implementation is considered fixed |
|---|---|---|
| CARET-H001 | `poll_multi_caret_manager` returns immediately unless status is `running`, but can transition to `degraded`. Later survivor changes are therefore not polled through this function. [R9] | Launch a real two-child team; terminate one; observe degraded; terminate the survivor; repeated polling must reach the correct terminal state without a duplicate launch. |
| CARET-H002 | IDE interactive flags do not enter the editor's interactive launch path in the inspected IDE entry. [R1][R2] | Launch IDE in each declared interactive mode, observe a real frame/event loop, send input, and exit cleanly. Keep readiness probes non-interactive. |
| MUX-H001 | `smux_send_text` appends to the model buffer through `PaneRecord.feed`, rather than demonstrating a PTY write. [R10][R11] | Send a random nonce to a real child that transforms it. Assert the transformed child output, not local echo or appended input. |
| MUX-H002 | Pane/window focus functions test existence but do not mutate focus. [R10] | Focus changes must alter authoritative state and route input to exactly one target. |
| MUX-H003 | Startup timing is hard-coded; invalid capture creates a success-shaped row. [R10] | Timing comes from a monotonic clock or is explicitly unavailable. Unknown pane capture returns a typed error. |
| MUX-H004 | Pane close replaces a slot with an empty record and decrements the count without visible compaction in the API. [R10] | Close first, middle, and last panes; every survivor remains discoverable and writable. Verify service indexing before declaring a runtime defect; adopt generation-checked slots or correct compaction. |
| MUX-H005 | Several operations accept session/window/pane IDs but visibly validate only some IDs. [R10] | Reject cross-session and cross-window ID combinations, expired generations, and unauthorized attachments. |
| MUX-H006 | Manager and mux capacities differ. [R9][R11] | Admission either atomically reserves every required resource or launches nothing. Capacity exhaustion never creates phantom pane IDs. |
| GUI-H001 | The browser page initially reports `Connected` before a demonstrated session handshake. [R8] | Connecting, ready, disconnected, reconnecting, and failed are driven by transport/session events. |
| GUI-H002 | The shown browser handler clears the draft before request completion and always follows output to the bottom. [R8] | Failed delivery retains a recoverable draft; scrolling upward suspends follow mode; switching agents restores independent draft and scroll state. |

The older gap audit demonstrates that stale completion records have occurred in these lanes. Its August conclusions must not override the newer Slang record or the inspected source. Do not use LOC ratios, placeholder responses, generated screenshots, or zero-example test runs as feature acceptance. [R12][R13]

## 3. Research: useful precedents and their limits

| Reference | Verified behavior or design pattern | Application to Caret |
|---|---|---|
| VS Code Agents window | Separates session list, active chat, changes, and files; actions are scoped to the active session. [W1] | Adopt visible session identity and scope. Keep the user's left composer/right session layout instead of copying the exact geometry. |
| VS Code session management | Provides grouping, pinning, and filters for sessions. [W2] | Stable, pinnable roster; explicit attention filter; no unsolicited row movement while the user is typing. |
| VS Code Agent Host, August 26, 2026 | Separates session ownership from individual editor windows and uses snapshots followed by ordered actions. Local host lifetime still has product-specific constraints. [W3] | Use a shared session host and replayable state. Define Caret host lifetime explicitly rather than assuming all terminal processes survive application shutdown. |
| Zed external agents | Distinguishes ACP-integrated external agents from terminal-backed CLI/TUI threads. [W4] | Keep native terminal and structured sessions as different capabilities under one session model. |
| ACP | Defines a client/agent integration protocol. [W5] | Optional adapter at the provider boundary, not a replacement for Simple's internal ownership and runtime contracts. |
| WezTerm multiplexing | Separates mux domains and UI attachment. [W6] | A pane is a service resource; opening a second view attaches rather than spawns. |
| Codex App Server | Supports rich-client integration, streamed session events, and approvals. Its documentation marks experimental surfaces and provides version-specific schema generation. [W7] | Pin/test the installed CLI schema. Prefer a local controlled transport initially; retain the native PTY path. |
| Claude programmatic and SDK interfaces | Provide streamed output and mechanisms for approvals and questions. [W8][W9] | Normalize events and distinguish permission decisions from conversational questions. Do not assume every installed version exposes every control. |
| VS Code shell integration | Adds command boundaries, working-directory information, and exit-status-related UI. [W10] | Offer optional sosh/shell integration for navigation, not as authority for provider permissions or task correctness. |
| xterm.js flow control and security | Documents producer overload, watermarks, and terminal web-context risks. [W11][W12] | Bound every queue, preserve parser integrity, and isolate terminal data from privileged actions. This is a reference, not a mandate to use a JavaScript terminal. |
| Microsoft ConPTY | Documents lifecycle and shutdown deadlock considerations when output is not drained. [W13] | Isolate blocking platform work and test Windows teardown with concurrent output draining. |
| W3C accessibility guidance | Provides contrast and unobscured-focus requirements. [W14][W15] | Use measurable accessibility criteria rather than visual polish alone. |

**Research conclusion:** a thin, shared workbench over persistent services fits the request better than embedding separate agent dashboards. Terminal fidelity and structured agent integration should coexist; neither should be faked by the other.

## 4. Default workspace composition

### 4.1 Desktop GUI

```text
+---------------------------------------------------------------------------------------------------+
| CARET / Simple IDE   Workspace: simple   Profile: Agents   Host: Local   Search / Commands   Settings |
+----------------------------+----------------------------------------------------------------------+
| AGENTS            [+ New]  | A2: Renderer repair   Claude CLI   worktree: agent/renderer   [Connected]|
| [Filter agents.........]   | [Terminal] [Activity] [Changes 4] [Files]     [Find] [Pin] [Stop] [...] |
| Attention 1   Running 2    +----------------------------------------------------------------------+
|                            |                                                                      |
| A1  Codex   Running        |                                                                      |
| A2  Claude  Needs approval |                       LARGE SELECTED SESSION                         |
| A3  Slang   Idle           |                                                                      |
| A4  Codex   Completed      |                 Native CLI terminal or structured view              |
|                            |                                                                      |
+----------------------------+                                                                      |
| SELECTED: A2               |                                                                      |
| Task: Renderer repair      |                                                                      |
| Model: provider-reported   |                                                                      |
| Branch: agent/renderer     |                                                                      |
| Permissions: Ask           |                                                                      |
| Pending: 1 approval       +-----------------------+-----------------------+----------------------+
| [Details] [Resources]      | A1 Codex / Running    | A3 Slang / Idle       | A4 Codex / Completed |
+----------------------------+  last visible rows    |  last visible rows    |  final visible rows  |
| TO: A2 / renderer          |  unread: 12           |  local / GGUF+ggml    |  exit: 0 / review    |
| [Message | Terminal paste]|  read-only preview    |  read-only preview    |  read-only preview   |
| [multiline draft........]  +-----------------------+-----------------------+----------------------+
| [Attach] [Expand] [Send]   | Other sessions: 3     [Previous] [Next]   Snapshot age / live indicator |
+----------------------------+----------------------------------------------------------------------+
| Focus: Composer -> A2   Mode: Message   Pending approvals: 1   Host health: Ready   Help             |
+---------------------------------------------------------------------------------------------------+
```

This is a layout specification, not a screenshot of an implemented application. The mode controls shown depend on verified provider capability. In terminal-only mode, “Send” becomes “Paste to A2” and does not imply structured delivery.

### 4.2 Geometry and responsive behavior

All measurements below are proposed design defaults, not existing implementation claims.

| Region | Desktop GUI | TUI |
|---|---|---|
| Left control column | Default 320 logical pixels; resizable, approximately 288–380 at ordinary desktop sizes | Default 34–40 columns when space permits |
| Roster | Flexible upper section; selected item remains visible | Approximately 8–14 rows; independently scrollable |
| Selected details | Compact summary with optional expanded inspector | 5–8 rows; secondary metadata behind Details |
| Composer | Anchored at bottom of left column; 4–8 text lines; expandable overlay | 3–6 text rows, explicit target and mode |
| Large session | Remaining right width; about 75–82% of right-side content height | At least 80 columns for full-layout target; height gets priority |
| Preview strip | Approximately 18–25% of right-side height, normally 2–4 visible cards | Typically 6–9 rows, 2–3 readable previews when wide enough |
| Global status | One restrained status line | One terminal row |

Use minimum-content rules, not rigid percentages. At high zoom or on a small display, preserving usable text takes precedence over preserving every panel simultaneously.

At roughly 1100 logical pixels or 120 terminal columns, collapse optional metadata before reducing the active session. Below that, offer a compact mode with the roster/details/composer in a drawer or tabbed control panel and the session full-width. At 80×24, use `Session`, `Agents`, and `Compose` views instead of microscopic previews. Switching views must preserve draft, target, scroll, selection, and terminal attachment.

On a short window, the composer and active session remain usable while the details section collapses. A long draft can open in a full editor overlay and returns to the same draft object. Do not permanently move the primary composer to the right in the normal layout.

### 4.3 TUI example

```text
 CARET  simple / Agents                     Local host: ready             F1 Help
+----------------------------------+-----------------------------------------------+
| Agents [filter.................] | A2 Claude / renderer / Terminal      [Stop]   |
| > A2 Claude  Needs approval      +-----------------------------------------------+
|   A1 Codex   Running             |                                               |
|   A3 Slang   Idle                |              ACTIVE TERMINAL                  |
|   A4 Codex   Completed           |                                               |
+----------------------------------+                                               |
| A2 / agent/renderer              |                                               |
| Permissions: Ask                |                                               |
| Pending approval: 1             |                                               |
+----------------------------------+-----------------------+-----------------------+
| To A2   [Terminal paste]         | A1 Codex              | A3 Slang              |
| [draft text...................]  | latest screen rows    | latest screen rows    |
| [Expand] [Paste to A2]           | read-only             | read-only             |
+----------------------------------+-----------------------+-----------------------+
 Focus: Composer -> A2   F6 Next region   Terminal keys: passthrough   Pending: 1
```

The runtime calculates cell widths using its Unicode-width policy. These ASCII sketches are conceptual and do not replace tested cell-grid layouts.

## 5. Screen and field specifications

### 5.1 Main screen: information hierarchy

| Surface | Always visible | Expanded or secondary information | User actions |
|---|---|---|---|
| Agent roster row | Stable agent ID/name, provider, explicit status text, attention/unread indicator | Task, worktree, model, last event age | Select, pin, filter, contextual actions |
| Selected-agent summary | Agent/provider identity, task, workspace/worktree, permission profile, pending action | Provider session ID, launch details, resource use, capability evidence | Inspect, open worktree, review pending item |
| Active session header | Target identity, surface type, connection state | Executable version, terminal dimensions, transport | Find, pin, detach view, explicit stop |
| Active session body | Actual provider terminal or native structured transcript | Tool details, diagnostics, review surfaces | Scroll, select/copy, follow output, interact |
| Inactive preview | Identity, state, readable screen excerpt, snapshot age | Unread count, last tool/result summary if verified | Activate or pin; no terminal input |
| Footer | Keyboard focus and input destination; attention count | Host health, resource-pressure notice | Open help or diagnostics |

The roster is not a miniature process monitor. CPU, RSS, GPU, token, and cost columns belong in a Resources inspector unless an abnormal condition needs attention. Unsupported metrics display `Unavailable` or `Not reported`, not a zero.

### 5.2 New Agent / Launch form

| Field | Control | Default and validation |
|---|---|---|
| Agent label | Text | Suggested readable label; internal identity remains immutable and unique |
| Provider | Picker | Codex, Claude, Slang, and configured compatible providers; show availability and probe failure reasons |
| Session surface | Picker | Native Terminal initially for CLI compatibility; Structured only when adapter capability passes |
| Workspace | Folder picker / TUI path entry | Explicit existing workspace; resolve and validate allowed roots |
| Worktree / branch | Existing picker or create-new fields | Recommend isolated worktree for write-capable parallel tasks; do not silently move the user's current checkout |
| Task / initial message | Multiline editor | Optional; retained through launch failures; explicit send-after-ready policy |
| Model | Provider-aware picker / advanced identifier | Do not invent or silently substitute model IDs |
| Permissions | Named profile with explanation | Safe interactive profile; no bypass-all default |
| Credentials | Reference to provider setup or secret store | Never a token embedded in a saved launch command or shared layout |
| Executable | Advanced path field | Resolved executable, version, and trust shown; validate before spawn |
| Local-model configuration | Model path/ID, device, memory limit, backend | Visible only for Slang; distinguish GGUF+ggml, native pack, and HTTP transport readiness |
| Lifetime | Attached / allow detached continuation | Explain host lifetime and explicit stop behavior |
| Resource limits | Optional advanced section | Admission validated against actual process, pane, transport, and model budgets |

The final action is **Launch**, not “Run command” over a concatenated shell string. The preview shows the executable and argument vector safely, with secrets redacted. Capability probing does not implicitly install software, download model weights, or grant trust.

### 5.3 Composer: separate message, provider command, workbench command, and terminal input

| Input intent | Destination | Behavior |
|---|---|---|
| Message | Caret/provider structured session API | Multiline text, attachments, explicit Send/Queue/Steer semantics based on capability |
| Provider command | Selected provider adapter | Discover supported commands; preserve provider semantics and scope. Never reinterpret an unknown provider command as a shell command. |
| Workbench command | IDE command registry | Command palette for split, attach, theme, session selection, and other UI actions |
| Terminal paste | Selected terminal input channel | Bracketed paste when supported; target visible; no implied submit or execution |
| Shell task | Explicit execution-service task | Separate action with argv/cwd/policy preview; not a hidden meaning of ordinary chat text |

The composer owns `Draft(session_id, session_generation, input_mode)`. On submission, capture the target and generation atomically. A focus change during serialization, queuing, or dispatch cannot redirect the message. An agent restart invalidates stale target generations.

For message mode, use Enter for newline and an explicit Send action; GUI can provide Ctrl/Cmd+Enter. TUI also exposes a visible command or function-key binding where enhanced keyboard protocols do not distinguish modifiers reliably. IME composition takes precedence: Enter that commits Hangul or another composition must not also send the message.

In native terminal mode, arbitrary text injection is not equivalent to sending a chat message. Without a verified provider prompt-control adapter, the left editor offers **Paste to A2**, and the user submits inside the terminal. A known, tested prompt mode may enable a separate “Paste and submit” action, but output heuristics alone cannot establish that it is safe. Busy or unknown terminal state must not silently accept a message as shell input.

Queued, delivered, acknowledged, rejected, and delivery-unknown are distinct. A lost acknowledgment must not trigger automatic re-execution when the provider lacks idempotency support. Keep the failed/uncertain draft available and present reconciliation choices.

### 5.4 Approval and question surfaces

Approvals are persistent attention items, not disappearing toast notifications. Show agent identity, provider request ID, tool, exact parameters, working directory, permission scope, network destination or file diff when applicable, and the reason approval is needed. Permit `Deny`, `Allow once`, and only provider-supported explicitly scoped alternatives. Resolve once using an approval generation/token; a second client cannot approve an already-resolved or expired request.

A provider question is a different surface: render supplied options and free text when supported, preserve multi-question grouping, and return a typed answer. Do not turn “Which branch?” into a permission grant. Claude's SDK explicitly distinguishes questions from tool-approval situations even when they use a common callback path. [W9]

Do not seize focus from an active draft when a background agent needs approval. Raise a stable badge, optional restrained notification, and an attention queue. Selecting the item opens its actual session context.

### 5.5 Other screens

| Screen | Content and input fields | Important invariant |
|---|---|---|
| smux Session Manager | Sessions/windows/panes, host, owner, attachment mode; filters; create/attach/split/rename/detach/terminate controls | Existing session attachment never becomes an accidental duplicate launch |
| Changes / Review | Changed files, revision-bound diff, test evidence, comments; staged decisions where supported | “Agent completed” does not mean changes were reviewed or tests passed |
| History / Recovery | Sessions, provider IDs, last checkpoint, lost connections, pending drafts; resume/reconnect/forget actions | Restoring metadata or transcript is not restoring an arbitrary live process |
| Resources | Process tree, measured memory, CPU, output backlog, device memory, model residency; sampling options | Attribute local-model and provider costs separately from UI overhead |
| Settings | Profiles, keymaps, theme, density, font/width policy, scrollback, privacy, launch policy, preview budget | Unsupported capabilities are explained, not represented as functioning toggles |
| Diagnostics | Versions, capability probes, recent transport errors, gate status, redacted export preview | No “all good” based only on a manifest or model fixture |

## 6. Professional visual and interaction system

Use a calm IDE aesthetic: restrained surfaces, one primary accent, semantic status colors, consistent typography, aligned labels, and little decorative motion. Reuse the IDE's theme tokens rather than hard-coding Caret-only values in HTML and terminal strings.

| Design element | Proposed rule |
|---|---|
| Spacing | Shared 4/8/12/16/24 logical-pixel scale; corresponding consistent cell padding in TUI |
| Typography | UI text approximately 13–14 logical pixels; terminal/editor approximately 14–16 by preference; never shrink all terminal text to make more previews fit |
| Surfaces | A small hierarchy: workspace, panel, selected/raised surface; thin separators; restrained corner radii |
| Color | Status has text/icon plus color; selected and focused are visibly different states |
| Theme set | Dark, light, and high-contrast; TUI truecolor, 256-color, 16-color, and monochrome fallbacks |
| Accessibility | Target at least 4.5:1 for normal text; ensure keyboard focus is visible and not hidden under overlays. [W14][W15] |
| Motion | Small optional transitions; reduced-motion mode; no continuously animated previews |
| Density | Comfortable and compact, both with usable focus targets and readable text |
| Empty state | Explain how to launch or attach; do not populate simulated agents in production |
| Failure state | Clear failed component, retained work, and supported recovery action; avoid generic infinite spinners |

Use one consistent semantic component set: `AgentRow`, `SessionHeader`, `SessionSurface`, `PreviewCard`, `TargetComposer`, `ApprovalPanel`, `ConnectionBanner`, and `ResourceInspector`. Share their state and actions, not necessarily identical drawing code.

Provide accessible transcript text and sensible announcement batching rather than reading every token or redrawing every status as a live-region announcement. TUI accessibility is constrained by the host terminal and assistive tooling; keep plain/linear output and structured transcript export available, and test actual combinations rather than claiming automatic GUI-equivalent support.

Key handling has explicit focus domains: workbench navigation, composer editing, and terminal passthrough. F6 can cycle regions by default but remains remappable. The terminal prefix and a “send this key to terminal” escape route are configurable. Do not globally consume Ctrl+C, Tab, Escape, Ctrl+Space, or provider shortcuts without a visible, documented routing rule. Ctrl+Space is particularly unsuitable as an unconditional global shortcut because it can belong to an IME. [W10]

## 7. Target architecture and ownership

```text
                    Simple IDE shared workbench
        +-----------------------+------------------------+
        | TUI renderer          | GUI renderer           |
        | shared semantic views, commands, focus, themes  |
        +-----------------------+------------------------+
                              |
                    Caret workspace plugin
                              |
                 snapshots / actions / acknowledgments
                              |
                Agent Manager / Caret session host
             sessions, tasks, approvals, drafts, recovery
                      /                       \
          Caret provider adapters          smux service
       Codex / Claude / Slang / ACP    sessions, panes, screen model,
                      |               attachments, previews, routing
                      +-----------------------+
                              |
                    Simple execution service
             process lifecycle, PTYs/pipes, cancellation,
               limits, credential/environment boundaries
                              |
                           SOSIX
              Linux/macOS PTY | Windows ConPTY | SimpleOS
```

This is a logical ownership diagram. It does not assume that every logical owner is a distinct OS process or that each child has the same physical parent relationship. Process supervision must track the actual platform process tree.

### 7.1 Responsibility contracts

| Owner | Owns | Must not own |
|---|---|---|
| Workbench kernel | Commands, focus, layout, subscriptions, accessible UI model, theme/settings | Provider SDK state, arbitrary process spawning, terminal credentials |
| Caret plugin | Agent-specific views and actions | A second process table or independent copy of session truth |
| Agent Manager | Logical agent/session lifecycle, launch policy, approvals, provider identity, recovery coordination | Terminal escape parsing or backend-specific drawing |
| Caret provider adapter | Provider protocol, native features, capability negotiation, normalized events | Global IDE state or unscoped shell execution |
| smux | Terminal identity, canonical grid/parser state, bounded scrollback, view attachments and input lease | Independent competing spawn/kill ownership |
| Execution service | Actual spawn/PTY/pipe handles, process-tree containment, wait/reap, stop escalation | Business interpretation of agent output |
| SOSIX | Platform I/O and process capabilities with async-first contracts | Caret-specific layout or provider policy |
| Slang worker/service | Model residency, inference, device admission, backend-specific memory | GUI event loop or terminal UI composition |

Reuse the existing execution owner if it already provides these contracts. `execd` is the architectural role, not a claim that a complete new daemon was verified in this inspection. Avoid creating a competing service under a new name.

### 7.2 Kernel/plugin and memory policy

The default workbench kernel should be small and statically composable. Use existing Simple composition/traits and plugin contracts; no new language syntax is required. First-party built-ins can use compile-time/static bindings; optional or third-party components use versioned capability contracts and worker isolation where appropriate.

Separate UI contributions from heavy service activation. Starting Caret should not activate Office applications, all language servers, every provider, model loading, or the compiler merely because capability entries exist. A registry description must be cheap to enumerate without loading its implementation.

The new control plane, terminal core, and service interfaces should be async-first and compatible with bounded nogc allocation. That does **not** mean the existing `gc_async_mut/slang` implementation or a third-party SDK has become nogc. Keep such components outside the workbench hot path, with memory separately accounted. A `slang_local` engine may remain in-process inside a Caret worker while still being out-of-process relative to the GUI.

Support explicit fixed-pool and growable-chunk policies through configuration. Preallocate ordinary session-control and terminal structures at admission. Dynamic extension must be bounded and observable. Pool exhaustion returns an error before spawning a partially representable session.

## 8. Session, state, and event contracts

### 8.1 Identity and state

Use opaque IDs with generations, not row indexes, bare PIDs, or mutable display names. A session view has a view ID; it references a logical session ID and generation; a terminal surface additionally references a terminal/pane ID and its generation; a provider adapter references its native provider session/thread ID when available.

| State dimension | Representative values | Why it is separate |
|---|---|---|
| Process lifecycle | NotStarted, Starting, Running, Stopping, Exited, Failed, Lost | Running process does not establish productive agent work |
| Agent turn | Idle, Queued, Working, WaitingApproval, WaitingAnswer, Completed, Cancelled, Failed, Unknown | Native terminal-only providers may not expose reliable semantic status |
| Transport | Connecting, Ready, Stale, Disconnected, Reconnecting, Closed | Disconnect is not evidence that the child exited |
| Capability evidence | Declared, Probed, Available, Verified, Unavailable, Failed | Metadata must not masquerade as tested integration |
| Delivery | Draft, Queued, Sent, Acknowledged, Rejected, Unknown | Prevent duplicate requests after reconnect |

A team may be degraded while individual members are alive. Continue reconciliation for nonterminal states, including degraded/error states with known possible survivors. When liveness is uncertain, show uncertainty and retain ownership records; do not claim the process is stopped merely because a signal was attempted.

### 8.2 Shared event envelope

This is a schema sketch, not verified Simple syntax:

```text
EventEnvelope {
  schema_version
  host_instance_id
  session_id
  session_generation
  source_id
  sequence_number
  monotonic_timestamp
  correlation_id
  payload
}

UserAction {
  action_id
  target_session_id
  target_generation
  expected_revision
  controller_lease
  payload
}
```

Use tagged payloads such as `SessionStarted`, `ProcessExited`, `TurnStarted`, `TextDelta`, `ToolStarted`, `ToolFinished`, `ApprovalRequested`, `QuestionRequested`, `UsageReported`, `TerminalUpdated`, `DeliveryAcknowledged`, and `SessionFailed`. Unknown additive payloads can be retained as opaque diagnostics when safe; unknown privileged actions fail closed. Bound payload sizes and nesting.

Clients receive a snapshot with its sequence boundary, then ordered updates. On a gap, request a new snapshot or a retained update range. Do not apply old-generation events to a replacement session. A delivery acknowledgment and a terminal output sequence are separate concepts.

Optimistic UI is acceptable for a draft or pending visual marker, not for claiming a permission has been granted, a child stopped, or a tool succeeded. The host's authoritative acknowledgment resolves the action.

### 8.3 Multiple viewers and one input authority

Allow several read-only observers. One attachment holds a generation-checked control lease for terminal input and PTY dimensions. The UI displays that owner; another window explicitly requests control. Selecting a preview does not silently take control from another client.

The same atomic resolution rule applies to approvals. Agent focus and keyboard focus are separate: inspecting agent B while a pinned draft targets A must leave a visible `To A` chip, and the submit action must use A's captured ID rather than whichever row was most recently selected.

## 9. smux in the IDE: functional scope

### 9.1 Required capabilities

| Capability | Initial production requirement |
|---|---|
| Terminal creation | A real PTY/ConPTY or declared equivalent, verified by child I/O |
| Sessions/windows/panes | Stable identity, validated hierarchy, atomic create/split/close |
| Attach/detach | Multiple observers; explicit controller; no duplicate process |
| Split/zoom/focus | Shared IDE layout model with accurate input destination |
| Resize | Debounced, clamped, generation-checked request to the actual terminal backend |
| Scrollback and find | Bounded retained history, copy mode, literal/regex search with resource limits |
| Input | Raw keys, text, paste, bracketed paste, correct mode-sensitive mouse handling |
| Terminal fidelity | VT parsing, alternate screen, cursor modes, SGR, supported keyboard/mouse protocols, Unicode widths |
| Persistence | Restore workbench layout and reconnect to a still-live host; separately support provider conversation resume |
| Shell integration | Optional command boundaries, cwd and exit status; sosh-first adapter plus tested host shells |
| IDE reuse | Build/test/debug terminals consume the same service; Caret is one client |

Do not advertise complete tmux configuration, control-mode, or key-table compatibility until its own compatibility suite passes. The inspected smux API explicitly lists several such features as deferred. [R10]

### 9.2 Preview correctness

**Each terminal stream has one canonical parser/screen model.** The active view and inactive cards consume screen snapshots or damage updates from that model. They do not each parse the stream, allocate an emulator, or start a provider.

A preview never resizes the provider PTY to its tiny card dimensions. Keep the last negotiated interactive dimensions while inactive, then resize when a legitimate controlling view becomes active and its final geometry is known. A card can crop a few readable screen rows or display a capped snapshot with an explicit native-size indicator. A transcript preview may instead show recent structured messages; label the surface type.

Suggested budgets are one snapshot refresh per second for TUI cards and up to two for visible GUI cards, only when dirty. Hidden cards do not paint. Attention state updates remain prompt even when preview imagery is throttled. These are paint budgets, not permission to stop consuming or correctly parsing process output.

### 9.3 Terminal core and platform boundaries

Prefer a shared terminal core with reusable model and parser contracts. Audit any existing terminal implementation before deciding whether to extend it or wrap a mature native library. A terminal-library choice needs its own conformance, license, build-size, and nogc/SFFI review; this plan does not mandate xterm.js, Electron, or a new renderer dependency.

GUI rendering should share the IDE's text/glyph resources, clipping, damage tracking, and presentation backend. Do not allocate a GPU swapchain per preview or per agent. TUI rendering emits minimal screen differences, restores terminal modes after failure, and keeps diagnostics out of the full-screen control stream.

Route OS operations through SOSIX-facing interfaces as the runtime unification progresses. Existing platform-specific imports can remain behind temporary adapters during migration; do not attempt a simultaneous all-platform runtime rewrite. The Windows adapter must account for ConPTY's documented output-drain/teardown constraints. [W13]

## 10. Provider integration and launch model

Every agent launch must pass through Caret's launch policy and provider adapter. Neither a preview nor a GUI widget directly launches `codex`, `claude`, or a local model.

| Provider lane | Initial path | Structured path | Acceptance boundary |
|---|---|---|---|
| Codex | Caret-managed native CLI in a real smux terminal | Version-pinned App Server adapter with ordered events and approval handling | Native PTY and structured protocol are tested separately; experimental upstream capabilities remain labeled |
| Claude | Caret-managed native CLI in a real smux terminal | Supported stream-json/SDK or another explicitly supported adapter boundary | Verify streaming, permission requests, questions, resume, cancellation, and provider-native command support for the installed version |
| Slang local | A Caret worker using `slang_local`, with the engine in that worker rather than the UI process | Typed in-process worker adapter or later shared inference-service client | Prove real tokens, admission, cancellation, and cleanup; show GGUF+ggml versus native-pack backend honestly |
| Slang HTTP | Caret adapter connecting to an explicitly configured or supervised local service | HTTP streaming where implemented | Do not promote from in-process evidence; require start/request/stop and no-leak checks |
| Other wrappers / ACP | Existing Caret adapter preserved or optional protocol plugin | Capability-dependent | Unsupported controls remain disabled with a reason; no provider-specific code in layout components |

Codex's current documented integration includes initialization, threads/turns/items, streaming notifications, and provider-originated approval requests. Generate or pin the schema matching the installed version rather than assuming all JSON-RPC dialects are interchangeable. Its documentation also warns about experimental server/transport surfaces. [W7]

Claude's documented CLI can emit streaming JSON, and SDK hosting exposes permission/question interactions. These mechanisms differ from embedding the interactive CLI. Preserve the provider's auth, native instructions, sandbox policy, and configuration; do not infer that a compatible message stream gives full native CLI parity. [W8][W9][W16]

### 10.1 One session, one authoritative execution

A structured conversation view and a raw terminal view may coexist only when they attach to the same real execution through supported mechanisms. Otherwise expose the surfaces that actually exist. Do not launch a second provider process just to draw a “Terminal” tab; do not synthesize provider terminal output from structured messages and label it native.

For a terminal-backed session, the primary screen is its real terminal. For a structured session, the primary screen is the structured conversation, with actual tool terminals or provider diagnostics as separate surfaces when available. Each tab displays what it represents.

Changing a provider or model is a capability-sensitive operation. Where live mutation is unsupported, offer an explicit new session or handoff with a preview of transferred context. Do not overwrite the old session's identity or imply its hidden provider state was transferred.

### 10.2 Local-model isolation without needless duplication

Keep Slang's large allocations away from the workbench process. Start with the verified worker-local transport so UI migration is not blocked on the unaccepted HTTP lifecycle. A worker can host one engine and one or more sessions only if its scheduling, cancellation, and memory accounting explicitly support that arrangement.

A shared model service can later avoid duplicated weights across several agents, but require independent context/KV ownership, per-session cancellation, admission, and fault containment. Do not evict another active session's model state silently. Show loading, ready, queued for memory, generating, cancelled, and backend failure separately.

The September 4 record is repository-reported evidence, not a benchmark performed here. The outstanding native-pack and HTTP-service gates remain distinct from the UI delivery. [R12]

## 11. Reliability and security hardening

### 11.1 Session and process lifecycle

| Failure | Required behavior |
|---|---|
| UI closed | Detach the view or ask about active sessions according to explicit policy; do not implicitly kill or duplicate them |
| Host remains alive, UI reconnects | Reattach by session identity and obtain a current snapshot plus ordered updates |
| Session host or execution owner dies | Show Lost/Unknown as appropriate; preserve records; reconcile actual ownership before offering restart |
| OS reboot | Restore layout/history and offer supported provider resume; never claim arbitrary terminal process restoration |
| Provider exits | Capture exit status and final events; drain streams; wait/reap; retain reviewable history |
| Partial team launch fails | Roll back created resources; show incomplete cleanup and survivors honestly |
| Cancel requested | Use provider-supported turn cancellation first when available; process-stop escalation is explicit and observable |
| Child ignores termination | Escalate through platform-supported containment; report failure if survivors remain |
| Network disappears after submit | Mark uncertain delivery, reconcile if supported, and never blindly resend a potentially mutating request |
| Disk is full | Preserve control-plane responsiveness; explicitly report unavailable persistence; do not claim durable save |

“Detach view,” “stop turn,” “terminate session,” and “delete history” are separate commands. A thumbnail close button must not be a concealed kill operation. A stopped process is confirmed through lifecycle evidence, not merely a successful signal request. POSIX process groups alone do not contain every possible daemonized descendant; use available stronger containment or report its limitation. On Windows, use appropriate job/process ownership and respect ConPTY teardown behavior. [W13]

### 11.2 Data, permissions, and hostile output

| Boundary | Required control |
|---|---|
| Terminal output to UI | Treat bytes as untrusted display data; bound escape-sequence length and parser work; do not execute text-derived UI commands |
| Terminal output to approval system | No text/ANSI parser can mint a trusted approval request or resolve one |
| Clipboard | Gate OSC clipboard operations; preview large/multiline pastes; avoid secret-bearing clipboard synchronization by default |
| Links and paths | Validate schemes, authority, workspace scope, and explicit user gestures; terminal links cannot automatically execute commands |
| Browser terminal | Use isolated, bundled code, safe text insertion, strong content policy, authenticated transport, and origin/host validation; loopback alone is not authentication [W12] |
| Launch requests | Structured argv, validated cwd, scoped environment, explicit credentials; no implicit shell interpolation |
| Workspace trust | Untrusted workspaces cannot silently start task/provider/plugin executables or broaden permissions |
| Provider policies | No default bypass-permission flag; preserve native provider safety controls and disclose unsupported enforcement |
| IPC | Authenticated local endpoint, per-client capabilities, session scoping, bounded messages, rate limiting, and revocable leases |
| Remote connections | Explicit opt-in and encrypted/authenticated transport; no unauthenticated public listener |
| Credentials and capture | No secrets in layouts or URLs; raw input logging off by default; redacted diagnostics with export preview |
| Recovery | Never replay approvals or mutating commands solely because they appear in a transcript |

Terminal redaction is not a guarantee that arbitrary secrets can always be detected. Limit retention and access first; make raw captures explicitly opt-in, visibly recorded, and bounded. A captured terminal stream may include secrets despite best-effort filtering.

### 11.3 Persistence

Persist versioned layout preferences, session metadata, optional provider-resume IDs, drafts according to privacy policy, and bounded audit/control events. Store raw terminal history separately from authoritative agent facts. Write checkpoints atomically and maintain a recoverable previous version.

Bind caches and drafts to workspace and session identities. On schema migration failure, preserve the original data, show the error, and offer a safe fallback layout. Do not run restored commands automatically. Do not rely on a serialized PID to prove a live process still belongs to the old session; require process birth/host-instance identity or platform handles.

## 12. Performance and resource design

### 12.1 Avoid the likely overhead traps

| Trap | Design response |
|---|---|
| Loading every IDE application for Caret | Profile-limited activation and demand-loaded services |
| Loading every provider SDK/model at startup | Metadata-only discovery followed by explicit probe/activation |
| Terminal emulator per thumbnail | One canonical model per terminal, shared snapshots/damage |
| Resizing PTYs for previews | Resize only from the controlling interactive view |
| Rebuilding the full roster each output chunk | Incremental keyed updates; stable ordering; coarse metric refresh |
| Rendering a full HTML page for every token | Retained/incremental view updates and batched text changes |
| Global polling and unconditional redraw | Event-driven wakeups, dirty regions, and explicit fallback polling budgets |
| Unbounded transcript/scrollback | Segmented retention with byte/line limits and capped indexes |
| Slow output consumer blocks all sessions | Per-session queues, fair scheduling, and a prioritized control path |
| GUI and provider memory mixed in reports | Separate workbench, service, provider-process, and model/device measurements |

No “zero overhead when hidden” claim is appropriate. A hidden terminal may still require input draining, parsing, storage management, and lifecycle monitoring. The achievable target is **no unnecessary painting or repeated preview construction**, with remaining work measured and attributed.

### 12.2 Backpressure and parser integrity

Use per-session high/low watermarks, bounded transport queues, and batched acknowledgments. Never discard arbitrary bytes from an ANSI or JSON stream: that can corrupt parser state and control messages. Process the authoritative stream correctly, then coalesce disposable view updates or require a snapshot resynchronization. Retained scrollback may evict complete old records according to policy. [W11]

If sustained producer throughput exceeds capacity, apply backpressure to that producer or spill within an explicit storage quota. If neither is possible, expose a clear failure/truncation condition and preserve parser safety; do not claim an intact transcript. Keep cancellation, approval responses, and host control on a path that does not wait behind an unlimited output backlog.

Service every session fairly. An output flood in one background agent must not starve input, another agent's approval, or another terminal. Parse budgets should be bounded per scheduling slice, but parsing continues independently of preview paint frequency.

### 12.3 Measurement plan

Measure these configurations on identical builds and machines: current Caret TUI, current Caret GUI, shared IDE alone, new Caret profile with no providers, one idle terminal session, four mixed sessions, sixteen sessions where capacity supports them, and Slang separately. Include cold and warm startup, small and large scrollback, all previews visible, minimized window, and output-flood conditions.

Record source revision, compiler/runtime and provider versions, build profile, backend, OS, display scale, terminal geometry, caches, session count, data fixture, and repetition count. Report distributions, not a single best run. Measure provider startup and model load separately from workbench first-frame time.

On Linux, report relevant RSS/PSS and process-tree measurements; on macOS, label physical-footprint measurements; on Windows, label private/working-set measurements. Do not present these different OS metrics as interchangeable. GPU/VRAM and shared model allocations require separate attribution.

Suggested initial engineering objectives, subject to baseline calibration:

| Metric | Proposed objective, not a measured result |
|---|---|
| Input-to-visible response | p95 below 50 ms under ordinary four-session use |
| Warm active-session switch | p95 below 100 ms without re-launch or provider restart |
| Input under background output flood | p95 below 100 ms while control remains usable |
| Active GUI update | Fit a 60 Hz frame budget when actively changing; no forced 60 Hz redraw while idle |
| Visible previews | At most 1 Hz TUI / 2 Hz GUI by default, dirty-only |
| Invisible previews | No painting or snapshot generation solely for invisible views; necessary stream processing continues |
| Memory growth | Bounded by configured pools, caches, queues, retained history, and explicit worker/model budgets |
| Lifecycle stress | No unreaped children or lost-owned resources across repeated launch/stop/detach/reconnect sequences |

A useful accounting model is:

```text
workspace_memory = shell + shared_services
                 + sum(session_control + terminal_screen + bounded_scrollback)
                 + shared_glyph_cache + bounded_preview_cache
                 + bounded_transport_and_event_buffers

provider_worker_memory and model/device_memory are reported separately.
```

Terminal cells may reference variable-size graphemes and attributes; do not assume a universal fixed per-cell size without measuring the chosen implementation.

## 13. Repository migration map

Paths in the “proposed destination” column are design targets, not claims that those files already exist. Reconcile them with the active repository's library taxonomy before starting moves.

| Existing owner | Proposed change / destination | Compatibility rule |
|---|---|---|
| `src/app/ide/main.spl` | Call shared workbench launch for interactive modes | Keep help, version, and explicit readiness/feature checks stable |
| `src/app/editor/main.spl` and GUI/TUI shells | Extract common workbench orchestration into `src/lib/editor/core/workbench.spl` and shared view/service modules | Editor remains a profile of the same services; no UI framework fork |
| `src/app/ide/plugin_manifest.spl` | Register Caret and terminal contributions through existing registry | Do not invent a new manifest format |
| `src/app/ide/feature_report.spl` | Add terminal and Caret real capability probes | Keep cheap metadata separate from live acceptance |
| `src/lib/editor/view/terminal_panel.spl` | Thin terminal view backed by a terminal service | Preserve callers during transition; remove line-buffer emulation as a production terminal claim |
| `src/os/apps/smux/{api,service,contract,buffer}.spl` | Extract reusable contracts/core into `src/lib/common/terminal_mux/`; async service into `src/lib/nogc_async_mut/terminal_mux/` | Keep OS-app facade and CLI; host IDE must not depend on a SimpleOS-app implementation |
| New IDE terminal adapter | `src/lib/editor/services/terminal_service.spl` | One service used by Caret, builds, tests, debug, and ordinary terminals |
| `src/app/llm_caret/main.spl` | Preserve noninteractive paths; select IDE Caret profile for migrated interactive modes | Existing flags continue through documented adapters |
| `src/app/llm_caret/multi_caret_manager.spl` | Fix reconciliation; adapt to authoritative session state | Do not discard corrected rollback/stop behavior |
| New Caret workbench contribution | `src/app/llm_caret/workbench/` with shared view-model/actions | Provider details remain in adapters, not GUI/TUI layout code |
| `src/app/llm_caret/gui.spl` | Compatibility frontend during migration; retire duplicated product composition after parity | Retain safe rendering and endpoint compatibility until a declared removal |
| Existing Slang entry points | Worker-bound adapter and capability reporting | No compulsory native engine rewrite as part of UI migration |

Add fallible, checked terminal APIs where old return types cannot express errors. Migrate callers before removing old interfaces. A compatibility wrapper may preserve a truthfully representable result; it must not manufacture success to preserve a test's shape.

Proposed CLI affordances include `simple ide --profile caret --tui` and `simple ide --profile caret --gui`. The `--profile` route is a proposal. Existing `caret --tui`/GUI entry points can select the same profile after migration. Keep prompt-only and server modes free of workbench activation.

## 14. Phased implementation and exit gates

| Phase | Deliverable | Exit gate |
|---|---|---|
| P0: Baseline and truth | Pin revision, runner provenance, current behavior, missing real evidence, defect reproductions, resource baseline | Known gaps are explicit; zero-example or placeholder evidence cannot pass |
| P1: Contracts | Identity/generation model, shared actions/events, lifecycle states, terminal owner API, capacity admission, UI semantics | Contract tests and reviewed ownership map; no two spawn owners |
| P2: Live IDE + smux | Persistent IDE workbench, real terminal I/O, attach/focus/resize/close, scoped input | Real nonce-transform child, real resize observation, survivor discovery, clean teardown |
| P3: Caret TUI | Requested composition, per-session drafts, native CLI sessions, read-only previews, attention flow | Keyboard-only workflow works with real sessions; no wrong-target input |
| P4: Caret GUI | Same state/actions, responsive docking, IME, accessible controls, incremental drawing | DPI/resize/input/recovery suite and visual comparison pass |
| P5: Structured adapters | Individually gated Codex, Claude, Slang capabilities, questions/approvals, delivery reconciliation | Real installed-provider evidence per feature; unsupported states remain visible |
| P6: Recovery and load | Multi-client leases, reconnect, persistence failures, stress, output floods, privacy/export | Chaos, performance, security, and no-leak gates pass |
| P7: Default migration | Route normal Caret UI into shared workbench; deprecate duplicate UI | Feature parity matrix signed off; rollback tested; old noninteractive commands preserved |

UI work can proceed against clearly labeled deterministic fixtures after P1. Such fixtures validate presentation and reducer behavior only. They cannot satisfy real process/provider gates.

Do not block P2–P4 on full Claude-CLI reimplementation, native Slang attention/KV-cache completion, a complete SOSIX rewrite, or optional remote protocols. Conversely, do not use UI readiness to claim those features are implemented.

## 15. Parallel-agent implementation plan

Pair a layer expert with a feature expert for each lane. These are proposed implementation work assignments, not agents launched during this report.

| Lane | Layer expert + feature expert | Main ownership | Depends on | Required evidence |
|---|---|---|---|---|
| A0: Integration/contracts | Runtime architecture + Caret workflow | Schemas, ownership, compatibility matrix, merge coordination | Baseline | Contract review and state-machine tests |
| A1: IDE workbench | Editor framework + agent workspace | Persistent launch, profiles, lazy activation, command/focus/layout services | P1 | Existing editor regression suite plus real IDE interaction |
| A2: Terminal core | PTY/ConPTY + smux | Checked API, process adapter, canonical grid, attach/control lease, capacity | P1 | Real I/O, resize, copy/find, lifecycle and cross-scope rejection |
| A3: Caret lifecycle | Process supervision + multi-agent | Manager reconciliation, launch/rollback, state normalization | P1 | Real partial-death and no-leak tests |
| A4: Provider adapters | Protocol integration + Codex/Claude | Version probes, native launch, structured sessions, approvals/questions | P1; A2 for native terminals | Recorded protocol fixtures plus separately run live-provider checks |
| A5: Local models | ML runtime + Slang/Caret | Worker isolation, backend identity, model admission, cancellation | P1; A3 | Real generation and cleanup; no HTTP/native-pack promotion from other evidence |
| A6: TUI | Terminal interaction + Caret UX | Layout, composer, focus, previews, compact mode | P1; integrate A1/A2/A3 | Cell-grid goldens and keyboard workflows |
| A7: GUI | Rendering/accessibility + Caret UX | Responsive layout, IME, DPI, damage updates, native controls | P1; integrate A1/A2/A3 | Pixel/semantic assertions and real input/platform tests |
| A8: Independent hardening | Test/security/performance + user workflow | Chaos, provenance, test integrity, perf measurements, adversarial output | Starts at P0 | Independent acceptance report and reproducible artifacts |

A0 owns shared schemas and serializes interface changes. UI agents do not edit provider launch internals. Provider agents do not alter UI reducers independently. A8 must not weaken acceptance criteria to make its lane green.

Use one isolated branch and worktree per lane/session, for example `feature/caret-workbench/a2-smux`. Separate move/rename commits from behavior changes. Rebase or merge against a known integration revision and verify that previously fixed specs were not silently replaced. Keep feature tests and layer tests linked in the existing documentation/SSpec taxonomy.

Run compile discovery across the entire changed/affected scope to collect the complete error inventory. Iterate on failing units first, then rerun affected suites, then the complete required acceptance set. A bootstrap runner limitation produces `BLOCKED`, not a passing substitute. Record the compiler/runner build identity with each result.

## 16. Test matrix and acceptance evidence

| Test ID | Scenario | Oracle |
|---|---|---|
| IDE-01 | Start TUI/GUI through IDE and Caret profile | A real interactive frame accepts input and exits cleanly; readiness mode still returns |
| MUX-01 | Child nonce transformation | Observed output originates from the child and differs as expected from submitted input |
| MUX-02 | PTY resize | Child-observed dimensions match the active controlling view, not preview-card size |
| MUX-03 | Close first/middle/last pane | All survivors remain discoverable, focused correctly, and writable |
| MUX-04 | Invalid and cross-session IDs | Typed rejection; no fabricated capture or another session's output |
| MUX-05 | Two UI attachments | One execution, two views, one input owner; unauthorized writes rejected |
| MUX-06 | Capacity exhaustion | Atomic refusal before spawn or complete rollback with no phantom resources |
| CARET-01 | First child exits, then survivor exits | Degraded manager keeps reconciling and reaches the correct final state |
| CARET-02 | Stop fails or child survives | UI reports stop failure/uncertainty, not clean shutdown |
| INPUT-01 | Switch agents while submit is queued | Original target ID/generation receives the action exactly once or an explicit failure |
| INPUT-02 | Restart reuses a display name/PID | Stale messages and approvals cannot target the replacement generation |
| INPUT-03 | Hangul/CJK IME composition | Correct text; commit Enter does not submit a second action |
| INPUT-04 | Multiline paste and control keys | Correct terminal mode behavior; no unannounced shell execution or intercepted key loss |
| UI-01 | Background session requests approval | Attention indicator updates without stealing focus or redirecting the draft |
| UI-02 | Scroll upward during output | Follow mode stays paused; new-output affordance appears; selection remains stable |
| UI-03 | Many inactive sessions | Preview count is bounded; no duplicate launch; visible cards remain legible |
| UI-04 | 80×24, 120×40, 160×50 TUI | No overlap, hidden input, or negative-size layout; compact navigation works |
| UI-05 | Desktop resize and 100/125/150/200% scaling | No clipped composer, stale hit targets, or excessive PTY resize storms |
| UI-06 | Keyboard, high contrast, reduced motion | Complete workflow without mouse or status-color dependence |
| PROV-01 | Native Codex/Claude sessions | Original interactive workflow remains usable; child/process cleanup verified |
| PROV-02 | Structured approval and question | Correct typed response, exact target, exactly-once resolution, proper cancellation |
| PROV-03 | Unsupported/version-mismatched feature | Explicit unavailable state and safe fallback; no silent protocol guessing |
| SLANG-01 | Worker-local inference | Real non-fixture tokens, truthful backend label, bounded model admission, cleanup |
| SLANG-02 | HTTP service lifecycle | Separate real service start/request/stop/no-leak evidence; cannot reuse SLANG-01 |
| REC-01 | UI crash with live host | Reattach to same session without respawn or duplicate message |
| REC-02 | Host dies/reboot | Lost/resumable state is honest; no screenshot-based process resurrection |
| REC-03 | Lost request acknowledgment | Unknown delivery is reconciled or shown; no blind replay |
| SEC-01 | Malformed ANSI/OSC and long frames | Parser stays bounded; output cannot issue privileged commands or approvals |
| SEC-02 | Hostile links/clipboard/browser origin | Scoped denial and explicit user consent where required |
| PERF-01 | One background output flood | Input and controls for other sessions remain responsive; buffers stay bounded |
| PERF-02 | Repeated create/switch/detach/close | Resource counters return to expected bounds; child leaks and unbounded growth absent |
| EVID-01 | No tests discovered or fixture used for live gate | Gate fails or is blocked; never passes |

Test terminal conformance with alternate screens, split UTF-8 sequences, combining characters, wide CJK cells, emoji sequences, cursor movement, line wrapping, selection after resize, bracketed paste, and supported keyboard/mouse modes. Differential comparison with a reference emulator is useful but does not alone prove every behavior correct.

For TUI, store cell-grid snapshots with dimensions and width-policy version. For GUI, store semantic assertions plus screenshots at fixed font/backend/scale configurations; mask only genuinely nondeterministic regions. A screenshot without hit-testing, keyboard, and lifecycle checks is insufficient.

Each acceptance record should include revision, platform, runner/compiler identity, backend/provider version, whether a fixture or real process was used, expected versus executed tests, exit status, timestamps, artifact hashes, and cleanup observations. Performance records additionally include sample counts and distributions.

## 17. Rollout, compatibility, and release policy

Introduce the workbench behind an explicit profile/feature route. Keep the current UI available as a rollback target while the parity matrix is incomplete. The fallback must not reconnect by spawning an additional provider; it attaches through the same session host or clearly states that a transition needs a new session.

Retain existing provider configuration, credentials, session IDs, and noninteractive flags. Migrate session/layout data with schema versions and reversible backups. Changing the default UI is a release-visible change; publishing a new default must be coupled to real tests, not merely a visual redesign.

Release the useful local product before optional remote agents, AHP/ACP interoperability, complete tmux compatibility, or all-provider structured parity. Preserve extensibility through adapters instead of importing those optional dependencies into the default startup path.

### Definition of done

The new default is ready when a user can launch Codex, Claude, and a supported real Slang configuration through Caret; see and control them from the requested TUI/GUI layout; open the same smux sessions from IDE surfaces; switch views without duplicated execution; safely respond to supported questions/approvals; retain drafts and correct input targeting; detach/reconnect under the stated host-lifetime policy; and pass the declared lifecycle, accessibility, performance, and security gates.

Unsupported Slang backend/transport combinations and provider-specific features may remain unavailable, but their status must be explicit. A release cannot describe the entire suite as complete merely because its workbench shell is ready.

## 18. Requirements traceability and final decisions

| User requirement | Design coverage | Primary acceptance |
|---|---|---|
| Harden and improve Caret suite UI | Shared semantics, lifecycle truth, security, performance, tests | Sections 2, 6, 11, 12, 16 |
| Use Simple IDE framework | Caret workbench profile, shared commands/focus/layout/settings, reuse existing editor | P1–P4; IDE-01 |
| Add smux terminal feature to IDE | Generic terminal service with real I/O, panes, attachments, copy/find, lifecycle | MUX-01–06 |
| Research screen layout and fields for TUI/GUI | Default geometry, responsive modes, per-screen/field specification | UI-01–06 |
| Left agent state/details/message-command field | Fixed primary composition with target-bound composer | INPUT-01–04; UI-01 |
| Large active session, small inactive sessions on right | Shared canonical terminal model, read-only bounded previews | MUX-02/05; UI-03 |
| Launch sessions through Caret wrappers or Slang | Provider adapters, single authoritative execution, worker isolation | PROV-01–03; SLANG-01/02 |
| Migration and GUI hardening plan | Source map, phases, independent agent lanes, rollback and release gates | P0–P7; REC/SEC/PERF/EVID tests |

**Final recommendation:** make the workspace attractive by making its hierarchy clear and its behavior trustworthy. The highest-value initial milestone is not a prettier browser chat card: it is **a genuinely interactive Simple IDE profile with real smux terminals, the requested agent layout, correct input ownership, and truthful status**. Then add structured provider richness without sacrificing terminal fidelity or startup isolation.

## 19. Limitations of this report

This report inspected selected source files at the pinned revision and current primary documentation. It did not build Simple, run its specs, start a provider, launch a GUI, verify the reported Slang experiment independently, or measure memory/startup performance. Defect candidates and suggested budgets must be tested on the target builds and platforms.

The source branch may continue changing after the pinned revision. Before implementation, revalidate each finding and resolve overlapping work rather than overwriting it. Treat external provider protocols as versioned and potentially changing. New paths, APIs, CLI profile flags, state models, and thresholds in this report are proposals, not claims of landed code.

## 20. Sources

Repository references are pinned to the inspected revision. External references are primary documentation consulted on 2026-09-05. The August gap audit and September Slang update are repository-authored records and are identified as such.

### Repository evidence

| Reference | Inspected file and relevance |
|---|---|
| [R1] | `src/app/ide/main.spl` — IDE entrypoint and readiness behavior. |
| [R2] | `src/app/editor/main.spl` — Existing interactive editor launch paths. |
| [R3] | `src/app/editor/gui_shell.spl` — Shared editor GUI shell and event/render loop. |
| [R4] | `src/lib/editor/view/terminal_panel.spl` — Current line-buffer terminal panel. |
| [R5] | `src/app/ide/plugin_manifest.spl` — Reuse of the existing plugin manifest registry. |
| [R6] | `src/app/ide/feature_report.spl` — Capability reports and separate live-state reporting. |
| [R7] | `src/app/llm_caret/main.spl` — Caret provider/UI modes and current launch contract. |
| [R8] | `src/app/llm_caret/gui.spl` — Current browser chat and native HTML helper. |
| [R9] | `src/app/llm_caret/multi_caret_manager.spl` — Parent-owned manager, capacity and lifecycle transitions. |
| [R10] | `src/os/apps/smux/api.spl` — Current smux session/pane API behavior. |
| [R11] | `src/os/apps/smux/service.spl` — smux fixed-capacity service state and buffer ownership. |
| [R12] | `doc/08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md` — Slang record updated September 4: real in-process inference and remaining gates. |
| [R13] | `doc/09_report/caret_smux_slang_agent_manager_gap_audit_2026-08-24.md` — Historical gap audit; not independent acceptance evidence. |

### External primary documentation

| Reference | Subject |
|---|---|
| [W1] | VS Code agent-workspace layout. |
| [W2] | VS Code session management. |
| [W3] | VS Code agent host architecture, August 26, 2026. |
| [W4] | Zed external agents and terminal threads. |
| [W5] | Agent Client Protocol overview. |
| [W6] | WezTerm multiplexing domains and attachment. |
| [W7] | OpenAI Codex App Server integration documentation. |
| [W8] | Claude programmatic/headless operation. |
| [W9] | Claude Agent SDK permissions and user-input requests. |
| [W10] | VS Code terminal shell integration. |
| [W11] | xterm.js flow control and producer/consumer buffering. |
| [W12] | xterm.js terminal security guidance. |
| [W13] | Microsoft ConPTY session lifecycle and I/O. |
| [W14] | W3C contrast-minimum guidance. |
| [W15] | W3C focus-not-obscured guidance. |
| [W16] | Claude CLI input/output and session options. |

[R1]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/ide/main.spl
[R2]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/editor/main.spl
[R3]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/editor/gui_shell.spl
[R4]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/lib/editor/view/terminal_panel.spl
[R5]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/ide/plugin_manifest.spl
[R6]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/ide/feature_report.spl
[R7]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/llm_caret/main.spl
[R8]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/llm_caret/gui.spl
[R9]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/app/llm_caret/multi_caret_manager.spl
[R10]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/os/apps/smux/api.spl
[R11]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/src/os/apps/smux/service.spl
[R12]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/doc/08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md
[R13]: https://github.com/ormastes/simple/blob/ea4fb1eb3d7e0b83db136d958e3d25dd667236a7/doc/09_report/caret_smux_slang_agent_manager_gap_audit_2026-08-24.md
[W1]: https://code.visualstudio.com/docs/agents/run/agents-window
[W2]: https://code.visualstudio.com/docs/agents/run/sessions/manage-sessions
[W3]: https://code.visualstudio.com/blogs/2026/08/26/agent-host-architecture
[W4]: https://zed.dev/docs/ai/external-agents
[W5]: https://agentclientprotocol.com/protocol/v1/overview
[W6]: https://wezterm.org/multiplexing.html
[W7]: https://developers.openai.com/codex/app-server
[W8]: https://code.claude.com/docs/en/headless
[W9]: https://code.claude.com/docs/en/agent-sdk/user-input
[W10]: https://code.visualstudio.com/docs/terminal/shell-integration
[W11]: https://xtermjs.org/docs/guides/flowcontrol/
[W12]: https://xtermjs.org/docs/guides/security/
[W13]: https://learn.microsoft.com/en-us/windows/console/creating-a-pseudoconsole-session
[W14]: https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum.html
[W15]: https://www.w3.org/WAI/WCAG22/Understanding/focus-not-obscured-minimum.html
[W16]: https://code.claude.com/docs/en/cli-reference
