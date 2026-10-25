# Caret to smux compatibility: actual caller audit

Date: 2026-10-25. Baseline release/1.0.0 commit
1e431722b40236eda5e80bd5f5bf06395b0d0d08. User scope: all Caret tmux usage
must work through smux in the same way. Status: SOURCE AUDIT; native execution
UNRUN. No genuine Phase3 producer is available to this audit. No seed or Phase2
substitute was invoked. Concurrent geometry, notifications, remote and target
changes are owned by other lanes; their presence is not qualification evidence.

## Execution paths and misleading apparent coverage

| Caller | Actual behavior | Compatibility consequence |
|---|---|---|
| agent_tmux.spl:26–56 | Builds/renders common.tmux_session_model values from already-owned agent processes | No tmux executable or PTY is launched; rendered pane rows cannot prove command support |
| pane_backend.spl:17–21,216–235 | Default real in-process smux API; opt-in CS_PANE_BACKEND=tmux probes PATH and tmux -V, then invokes via Sosix | Working smux API adapter is not a tmux command adapter; unavailable opt-in silently falls back to smux |
| workbench/pane_team.spl:126–164 | Creates/splits smux slots and starts one real pipe child per agent; errors roll back owned batch | Real process path, but not the dashboard PTY path or tmux CLI parity |
| agent_workspace.spl:65–68,86–180; workspace_cli.spl:112 | Real tmux process calls on private socket caret_ws_ID; CLI rejects missing tmux | This additional caller must be included; dashboard-only replacement leaves workspace unusable |
| claude_full/utils/swarm/backends/TmuxBackend.spl:33–110 | Appends command strings, creates synthetic %leader-N/%swarm-N IDs, returns true; no host execution | Model scaffolding, not a working smux or tmux backend; lock/readiness helpers return constants |
| same directory/PaneBackendExecutor.spl:36–76 | Type-name availability, synthetic type:agent@team IDs, in-memory mailbox and command records | spawn success does not prove child existence; kill/isActive bookkeeping is not lifecycle execution |
| claude_full/utils/terminalPanel.spl | State/log model with supplied detection status | Persistent terminal panel model is not native server evidence |
| messageActions/LogoV2/terminalSetup/configConstants | Display labels, command presentation and environment/UI metadata | Do not mistake displayed tmux text or parity ledgers for executed commands |

The hosted product entry src/app/hosted_apps/smux_client.spl accepts only
--serve ADDRESS TOKEN, --request ADDRESS TOKEN VERB..., --attach ADDRESS TOKEN
SESSION CLIENT_ID, --help, or stdin-owner mode. Unknown argv returns1.
src/os/apps/smux/smux_api.spl merely defines command/response values with names
such as new-session; it does not parse or execute the commands below. Renaming
smux.exe to tmux.exe therefore cannot satisfy current callers.

## Real Caret command/flag/result matrix

The strings below describe argv elements, not shell text to split again. Keep
literal arguments, command argv, empty arguments, spaces and Unicode intact.
All real callers use zero process status as success. WorkspaceResult errors
retain stdout+stderr; dashboard failures return false/empty Pane/empty list.

| Commands and exact used options | Caller/result contract | Current smux obligation |
|---|---|---|
| -V | pane_backend:216 and agent_workspace:86 require exit0, actual availability | Add compatibility version/probe through selected backend, not hardcoded success |
| -L caret_ws_ID COMMAND; modeled -L claude-swarm | workspace prefixes every command; private kill-server must not affect other owners | Persistent named server namespaces, authentication/ownership and process-independent endpoint discovery |
| has-session -t SESSION | workspace existence is exit0; absent is nonzero | Target resolution plus status-only probe |
| new-session -d -s SESSION -c CWD | workspace creates default shell detached; repeated ensure first probes existence | Honor CWD and detached persistent lifecycle; no launch in caller directory by accident |
| new-session -d -s SESSION -P -F '#{pane_id}' CMD ARG... | pane_backend:543–559 consumes trimmed stdout starting %, then lists same pane | Emit real globally unique pane ID only; launch supplied argv; no smux status prose in stdout |
| list-windows -t SESSION -F '#{window_name}' | workspace compares each trimmed line to exact name, deliberately avoids prefix ambiguity | Exact names and one row per window |
| new-window -d -t SESSION -n NAME -c CWD [COMMAND] | workspace supplies optional single shell-command argument | Preserve shell-command versus argv invocation semantics and CWD |
| split-window -d -t SESSION:WINDOW -c CWD | workspace creates another pane in named window | Resolve target and detached focus semantics |
| split-window -d -t SESSION -P -F '#{pane_id}' CMD ARG... | dashboard requires real returned ID and subsequent list visibility | Same printed-ID/argv contract as session creation |
| list-panes -t SESSION -F PANE_FORMAT | dashboard parses ID, numeric PID, active0/1, zoom0/1, then rejoins title tokens | See exact format section; no filtering unexpected by tmux contract |
| list-panes -s -t SESSION -F '#{session_name}:#{window_name}.#{pane_index} #{pane_id}' | workspace enumerates all windows; excludes exact TMUX_PANE, broadcasts to first target column | Session-wide enumeration, stable indexes, globally unique IDs and inherited TMUX_PANE |
| select-pane -t %ID; select-pane -t %ID -T TITLE | dashboard focuses, assigns title after creation | Real owner focus/title mutation, persisted metadata |
| resize-pane -Z -t %ID | dashboard toggle; zoom is window property and only active pane reports maximized | Actual window zoom/unzoom and child geometry, not local flag alone |
| resize-pane -t TARGET -x COLS -y ROWS | dashboard/std wrappers require successful terminal dimensions | Real geometry/provider resize and accurate refusal |
| kill-pane -t %ID | dashboard requires success only on owned child/pane teardown | Last-pane/window/session lifetime must match command semantics; separate compatibility policy from reusable internal slots |
| send-keys -t %ID -l BODY; send-keys -t %ID Enter | dashboard literal payload then separate Enter; no Enter after failed literal delivery | Literal mode must never interpret BODY as named keys; preserve two operations |
| send-keys -t TARGET COMMAND Enter | workspace uses default named-key semantics, not literal flag | Preserve caller's default tmux key parsing, do not silently rewrite as paste |
| send-keys -t %ID KEY | dashboard Enter Escape Tab Space Up Down Left Right C-c | Named-key mapping, control bytes, unknown-key error, correct addressed child |
| capture-pane -p -J -t %ID -S -N [-e] | dashboard splits stdout by newline, preserves styled output when -e | Joined wrapped lines, negative history start, ANSI rendition, no protocol header |
| capture-pane -p -J -S - -t TARGET | workspace polls marker in all available history | Entire retained history selector '-', joined lines and asynchronous real child output |
| kill-server | workspace teardown under its -L namespace | Stop only private server and all its owned resources; other server remains live |

Dashboard PANE_FORMAT at pane_backend.spl:137 is exactly
`#{pane_id} #{pane_pid} #{pane_active} #{?window_zoomed_flag,#{pane_active},0} #{pane_title}`.
Its parser (:154–177) rejects IDs not starting %, nondigit PIDs and flags other
than0/1; title spaces are normalized by its existing token rejoin. Do not change
that parser to accept smux's unrelated default list output. Format evaluation
must support nested conditional substitution here, rather than recognizing only
one hardcoded complete template. A zero exit with malformed output is failure.

## Standard tmux wrappers and additional model contracts

std.nogc_sync_mut.tmux.mod is the implementation; nogc_async_mut reexports it,
gc_async_mut reexports that, gc_sync_mut reexports gc_async_mut. It currently
builds shell commands through std.io_runtime, hardcodes tmux and POSIX quoting.
No direct import from the audited live Caret dashboard/workbench was found;
these remain required shared-wrapper compatibility surfaces, not proof that
all their functions were invoked by Caret in this audit.

| Wrapper call shapes | Parsed result/behavior |
|---|---|
| command -v tmux; list-sessions | availability/server existence via exit status |
| list-sessions -F '#{session_name}\|#{session_windows}\|#{session_attached}\|#{session_created}' | Four pipe-separated fields; numeric window count and attached flag; created retained as text (backslashes here only escape Markdown table separators) |
| list-windows -t SESSION -F '#{window_index}\|#{window_name}\|#{window_active}\|#{window_panes}' | Numeric index/pane count and0/1 active |
| list-panes -t SESSION:INDEX -F '#{pane_index}\|#{pane_active}\|#{pane_width}\|#{pane_height}\|#{pane_current_command}\|#{pane_pid}' | Six fields, real dimensions/current child command/PID |
| new-session -d -s NAME; new-window -t SESSION -n NAME | Success is status0; new-window then display-message -t SESSION -p '#{window_index}' yields numeric index |
| split-window -h/-v -t SESSION:WINDOW; split-window -t TARGET COMMAND | Follow-up display-message -t TARGET -p '#{pane_index}' must identify actual pane; retain active-target behavior |
| display-message -p '#{session_name}:#{window_index}.#{pane_index}' | Current client/active context, not arbitrary first session |
| capture-pane -t TARGET -p -e [-S NEGATIVE]; display-message -t TARGET -p '#{pane_height}' | Plain stdout content; row count from actual height or requested history count |
| kill-session -t NAME | Wrapper first probes pane_current_command and refuses claude/codex/simple_mcp/simple_lsp; preserve that protection |
| send-keys default/-l; resize-pane -x/-y | Same key, literal text and real resize contracts as above |

The modeled swarm backend additionally requires split-pane -h (alias intent),
select-pane -P fg=COLOR, select-pane -T NAME, set-option -w -t WINDOW
pane-border-status top, select-layout even-horizontal/main-vertical, break-pane
-d -s PANE, join-pane -s PANE, and scoped kill-pane. Color mapping is purple to
magenta, orange to colour208, pink to colour205. Do not turn its fabricated pane
IDs or string concatenation into a transport protocol; replace model execution
with actual owner results once a shared adapter exists. Its cached
leader:swarm-view and fixed200ms readiness/constant lock methods are not valid
substitutes for current-window lookup, actual readiness or synchronization.

## Existing in-process smux adapter differences

- pane_backend._smux_scope selects only the first window. _smux_list filters
  out dead children and gets title/PID from process-local _smux_info, unlike
  server-owned list metadata. Those values disappear with the dashboard.
- pane_zoom:369–378 only toggles _smux_zoomed after existence check; it does
  not invoke a real smux window zoom or resize. This is a concrete false
  equivalence for resize-pane -Z, even though UI may display a maximized pane.
- pane_kill:383–401 deliberately retains the last empty slot for later reuse.
  This internal convenience must not redefine kill-pane CLI lifecycle.
- pane_send uses smux_paste_text (bracketed paste if enabled), a delay and CR;
  the tmux branch uses literal send-keys then Enter. Interactive applications
  can distinguish paste from literal keystrokes; parity needs a deliberate
  test and compatible literal route, not just identical visible text.
- In-process smux depends on polling/capture to drain children (cs_dashboard
  comments:547 onward); independent persistent server behavior is a separate
  owner. Workspace processes cannot share its local _svc by importing the API.
- Windows spawn command-line quoting and POSIX private launch scripts are real
  implementations, not stubs. Keep their argv/environment/error/cleanup
  behavior while adding compatibility; no shell re-splitting shortcuts.

## Check-script evidence boundary

The check-llm-caret*.shs audit found no direct tmux command launch in those
wrappers. check-llm-caret-acceptance.shs:93 includes
caret_suite_tmux_window_system_spec.spl, which calls agent_workspace, creates a
private server/window, runs a real suite, polls capture-pane for Results and
cleans up its server. A missing tmux currently becomes pending; that is not a
smux pass. check-llm-caret-tui-pty.shs uses the host script utility (:554–567),
not tmux; its PTY/editing/invalid-UTF8 controls do not establish multiplexer
command equivalence. Infra-live's tmux mention promises not to touch the server.
CLI/native closure/parity-plan checks similarly cannot replace real pane tests.

## Implementation proposal and admission criteria

No small isolated adapter file can honestly close this matrix today: the CLI
parser, format evaluator, persistent socket namespace and owner metadata must
agree. Do not add an unused adapter or report fake success to reduce the scope.

1. Add one pure command parser/formatter capsule under os.apps.smux for this
   complete caller vocabulary, with typed argv/target/format structures. Keep
   new standard structured records in SDN; compatibility stdout remains tmux's
   requested text format. Coordinate root target/remote owner before edits.
2. Add an actual hosted compatibility entry through synchronous Sosix. Map -L
   namespaces to independently owned authenticated servers; preserve cwd, real
   child argv, global pane IDs/indexes, titles/PIDs/current commands, client
   context and error status. Do not flatten argv with join(" ").
3. Wire existing dashboard/workspace and shared tmux wrappers through this
   selected backend without changing their option, parsing or lifecycle
   contracts. Preserve opt-in tmux for differential testing. Replace modeled
   swarm success with real owner execution, keeping existing API signatures.
4. Geometry owner supplies true zoom, hide/show/rebalance; notifications owner
   and root target/session owner integrate their scopes. Audit host calls at
   these seams: existing app.io process owners are not permission to introduce
   raw externs; new product host access must remain Sosix-owned.
5. With genuine admitted Phase3, execute each matrix row once against isolated
   smux owner(s), and tmux where available, comparing command status, parsed
   fields and real child side effects. Required controls include two -L owners;
   private kill isolation; detached client exit/reconnect; actual cwd/argv with
   spaces/Unicode/empty args; global ID versus indexed target resolution;
   conditional formats; real zoom/restore/resize; literal Enter/C-c strings vs
   named keys; failed write must not submit; wrap joining/history/ANSI; dead
   pane listing; last-pane cleanup; child output after detached clients;
   hidden pane survival/join and real process exit. Retain full native command,
   producer/runtime hashes, assertion counts and quiescent cleanup receipts.

Completion remains blocked on implementation and genuine native execution;
this report does not claim general tmux parity or reduce the user's scope.
