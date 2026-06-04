# Editor IDE Restart Plan - 2026-05-13

## Goal For New Session

Continue the production Simple editor / IDE work from the current partial state.
The target is a production editor with:

- Obsidian-style Markdown visual inline editing.
- VSCode-like, extensible MDSOC-friendly IDE infrastructure.
- Debug Adapter Protocol support for Simple programs.
- Markdown and Simple LSP support for diagnostics, definition, completion, quick fixes, and warnings.
- Performance-oriented startup and hot request paths.

Do not mark the overall goal complete until a fresh audit proves all items above
work end-to-end and the required verification gates pass.

## Current Verified State

The current session restored and verified a narrow DAP/editor/LSP slice:

- `src/app/dap/simple_dap_main.spl` exists as a launchable stdio DAP adapter.
- `scripts/smoke/dap_protocol_smoke.py` exists and drives initialize, launch, breakpoints,
  stack, scopes, variables, evaluate, and disconnect.
- `test/system/dap_protocol_live_spec.spl` exists and wraps the live smoke.
- Extension manifests now support `ExtensionDebugAdapter`.
- `simple-language` contributes the `simple` debug adapter:
  `src/app/dap/simple_dap_main.spl`.
- `ExtensionHost` registers and looks up debug adapters.
- LSP client/transport now have `textDocument/codeAction` request support.
- Markdown LSP advertises `codeActionProvider` and returns simple quick-fix actions.
- Editor controller has quick-fix/debug-start command routing and state fields.
- `src/lib/editor/services/simple_lsp_config.spl` was added as the Simple LSP config surface.
- Latest 2026-05-13 verification also has the full editor controller system
  spec green under the interpreter, plus native DAP process command/launch
  smokes and the LSP activation smoke green using
  `src/compiler_rust/target/debug/simple`.

Verified commands that passed before this handoff:

```bash
bin/simple check src/lib/editor/extensions/manifest.spl src/lib/editor/extensions/host.spl src/lib/editor/extensions/builtin/spl_language.spl src/lib/editor/extensions/builtin/md_language.spl test/system/editor_extension_spec.spl src/app/dap/simple_dap_main.spl test/system/dap_protocol_live_spec.spl
python3 scripts/smoke/dap_protocol_smoke.py
bin/simple test test/system/dap_protocol_live_spec.spl --mode=interpreter
bin/simple test test/system/editor_extension_spec.spl --mode=interpreter
bin/simple check src/lib/editor/services/lsp_transport.spl src/lib/editor/services/lsp_client.spl src/lib/editor/services/md_lsp_config.spl src/lib/editor/services/simple_lsp_config.spl src/lib/editor/services/diagnostics.spl src/app/md_lsp/md_lsp_handler.spl src/app/editor/commands.spl src/app/editor/editor_controller.spl
bin/simple test test/system/editor_controller_spec.spl --mode=interpreter
bin/simple test test/system/editor_md_lsp_code_action_spec.spl --mode=interpreter
bin/simple test test/system/editor_lsp_spec.spl --mode=interpreter
```

## Dirty Worktree Caveat

The worktree was already dirty. Do not revert unrelated changes.

Known unrelated dirty paths seen during handoff:

- `examples/**` submodule/worktree entries.
- `src/compiler_rust/vendor/zerocopy/win-cargo.bat`.
- `doc/03_plan/simple_browser_chrome_class_roadmap.md`.

The editor/DAP/LSP work currently touches:

- `src/app/editor/commands.spl`
- `src/app/editor/editor_controller.spl`
- `src/app/md_lsp/md_lsp_handler.spl`
- `src/lib/editor/extensions/builtin/md_language.spl`
- `src/lib/editor/extensions/builtin/spl_language.spl`
- `src/lib/editor/extensions/host.spl`
- `src/lib/editor/extensions/manifest.spl`
- `src/lib/editor/services/diagnostics.spl`
- `src/lib/editor/services/lsp_client.spl`
- `src/lib/editor/services/lsp_transport.spl`
- `src/lib/editor/services/md_lsp_config.spl`
- `src/lib/editor/services/simple_lsp_config.spl`
- `test/system/editor_controller_spec.spl`
- `test/system/editor_extension_spec.spl`
- `test/system/editor_lsp_spec.spl`
- `test/system/editor_md_lsp_code_action_spec.spl`

Before continuing, run `git status --short --untracked-files=all` and verify the
DAP files still exist. During the previous session, some untracked files
disappeared between operations.

## 2026-05-13 Production Parity Audit Update

The editor/DAP/LSP restart slice was useful but is not full production IDE
parity. Treat the previous work as a verified foundation only:

- Quick-fix apply now mutates the active buffer, records undo state, refreshes
  Markdown preview state, clears stale actions, and covers heading spacing,
  empty-link, and trailing-whitespace fixes with behavior tests.
- Markdown and Simple editor lifecycle now starts the matching LSP surface,
  sends `didOpen` and edit-time `didChange`, polls diagnostics, and exposes
  active-language completion, hover, definition, and code-action request paths.
- Simple LSP is verified as `bin/simple lsp`, with live protocol smoke coverage
  for initialize, didOpen, completion, definition, codeAction, shutdown, and exit.
- DAP smoke coverage now checks missing programs, invalid breakpoint lines,
  exception breakpoint filter binding, and unavailable evaluation results in
  addition to initialize, launch, breakpoints, stack, scopes, variables,
  evaluate, continue/step events, and disconnect.
- Markdown renderer behavior now covers inactive rendered blocks, active-block
  raw source preservation, and inline emphasis/code-span rendering without source
  mutation.
- Obsidian callout blockquotes now classify as callout blocks in the editor
  block model and render as typed TUI/GUI callout surfaces with behavior
  coverage; command/palette routing now toggles the active callout source
  marker between folded and unfolded states, and folded callouts hide body
  content in TUI/GUI rendering with GUI fold button metadata. Visual edit
  preservation and richer styling remain.
- Full-line Obsidian note embeds and Markdown image attachment embeds now
  classify as embed blocks in the editor block model and render as explicit
  TUI/GUI embed surfaces with metadata and behavior coverage. Resolved note
  embeds now render target document content in wiki-aware TUI preview and GUI
  transclusion surfaces while stripping frontmatter, and nested resolved note
  embeds render recursively with a depth cap. Markdown image embeds now render
  actual GUI image preview markup. Picker/storage UX and inline mixed-content
  rendering remain.
- Markdown table GUI preview rendering now emits structured table rows and cells
  instead of escaped table source, with behavior coverage. GUI table surfaces now
  expose editable cell metadata and row/column insertion controls that route
  through Markdown source mutations, and GUI table cell commit events update the
  backing Markdown with behavior coverage. Table-cell navigation is now
  command/palette/Tab covered for same-row next, previous, and cross-row
  separator-skipping next/previous movement; richer TUI table interaction
  remains.
- Markdown task list GUI rendering now emits checkbox controls with source-line
  metadata, and GUI `task-toggle` events update the requested Markdown task line
  through the editor buffer with behavior coverage. Task panels now support
  open/done/all filters plus active-buffer batch mark-done/open operations
  through command/palette and GUI controls; explicit vault-root task batch
  mark-done/open is command/palette-routed, updates Markdown files on disk,
  refreshes matching open buffers, and rebuilds the task panel from the vault
  index. Richer visual task query UI and visual editing polish remain.
- Wiki backlinks, tasks, tags, and graph edges now have command/palette routes
  that populate a shared `WikiPanel` and render in the right dock for both TUI
  and GUI shells from loaded Markdown notes.
- LSP definition, references, document symbols, and workspace symbols now route
  through a shared result panel model that can render parsed locations/symbols
  and pending async requests in both TUI and GUI right docks; selected result
  targets can be opened with `lsp-jump`, and normal-mode `j`/`k` can select
  rows while the LSP panel is active. The LSP client now retains completed
  response JSON, pops receive buffers from owned transport state, and TUI/GUI
  frame loops hydrate pending result panels when server responses arrive.
- Rename now has command-line/palette payload routing through `rename <newName>`;
  async `textDocument/rename` responses apply returned WorkspaceEdit content to
  the active buffer and disk-backed sibling files using the shared edit applier.
  `rename-preview <newName>` now hydrates returned WorkspaceEdit content into a
  pending review panel without mutating the buffer, and `rename-confirm` applies
  that pending edit with behavior coverage. GUI LSP preview panels now expose
  Apply/Cancel controls that route through the shared WorkspaceEdit confirmation
  and cancellation paths. Richer diff/conflict UI remains.
- Formatting now applies async `textDocument/formatting` and
  `textDocument/rangeFormatting` TextEdit-array responses into the active buffer
  through the shared edit applier. `formatting-preview` and
  `range-formatting-preview` now hydrate returned TextEdit results into a
  pending review panel before confirmation, with the same GUI Apply/Cancel
  controls as rename previews. `formatting-save` and
  `range-formatting-save` apply returned formatting edits and save the active
  file to disk with behavior coverage. Richer side-by-side formatting review UI
  remains.
- Multi-file LSP WorkspaceEdit quick fixes now synchronize edits into already
  open sibling buffers instead of only applying disk-backed sibling files. Open
  sibling buffers are marked dirty and keep the change in memory; closed sibling
  files continue to be updated on disk. Command-only and edit-plus-command LSP
  code actions now request `workspace/executeCommand` through the active language
  server after any edit application. Async LSP code-action responses now hydrate
  into a selectable Code Actions right-dock panel, and Enter applies the selected
  action. Richer filtering/grouping UI remains.
- Signature help now hydrates async `textDocument/signatureHelp` responses into
  the shared TUI/GUI LSP results panel, exposes a controller signature popup,
  renders escaped GUI popup markup, and supports command/Escape/GUI dismissal
  with behavior coverage. Insert-mode `(`/`,` trigger characters now request
  signature help after buffer mutation. TUI rendering now overlays a styled
  signature popup with behavior coverage. Active parameters are now extracted
  from `activeParameter`, carried in controller state, rendered as a GUI
  `.signature-active-parameter` span, and ANSI-highlighted in TUI output; richer
  multi-signature overload navigation remains.
- Selection ranges now have client/controller/command/MCP request routing, async
  `textDocument/selectionRange` hydration into the shared LSP result panel, and
  behavior coverage for nested returned ranges. `selection-expand` and LSP panel
  Enter apply the selected range into active buffer selection state, and TUI/GUI
  renderers show active selection highlighting. Insert/delete/backspace now
  replace or clear active selections with buffer behavior coverage. Default
  `Shift+Alt+Right` / `Shift+Alt+Left` chords now expand and shrink through
  controller, GUI, and SDL paths. Richer multi-cursor selection UX remains.
- Folding ranges now hydrate async `textDocument/foldingRange` responses into
  the shared TUI/GUI LSP results panel, apply returned ranges to buffer fold
  state, hide folded interior lines in TUI, GUI, and headless render paths, and
  expose behavior-tested fold-all, unfold-all, and current-section fold-toggle
  controls through editor and Markdown extension commands. Fold creation now
  remaps cursors hidden by the folded range back to the fold header. Fold state
  now serializes/restores from buffers, persists in session DB tab records, and
  reapplies during session DB restore. Folded header lines now show `+N folded | za`
  markers in TUI/headless output and GUI `.fold-badge` metadata. GUI fold badges
  dispatch `fold-toggle` events that unfold the exact represented range, and
  normal-mode `za` toggles the current Markdown section fold with behavior
  coverage.
- Document links now hydrate async `textDocument/documentLink` responses into
  the shared TUI/GUI LSP results panel with selectable targets, and Markdown
  `open-link`/normal-mode `gx` cursor hit testing opens local Markdown links and
  open-note wiki links. GUI Markdown rendering now emits link hit-test metadata,
  and GUI `link-click`/Ctrl+Click event paths open local Markdown/wiki targets;
  external browser handoff remains.
- Unresolved wiki links opened through `open-link`/`gx` now create a
  heading-seeded Markdown note in the active note directory before opening it;
  vault/index invalidation after create remains.
- Call hierarchy roots plus incoming/outgoing calls now hydrate async LSP
  responses into the shared TUI/GUI LSP results panel. Incoming/outgoing rows
  preserve hierarchy depth and render as indented direction-labeled child rows.
  Selected rows now expand/collapse and collapsed rows hide descendants with
  behavior coverage. Call-row expansion state now persists across async panel
  refresh/reconstruction, prepared rows retain the original LSP item payload,
  selected root expansion requests incoming calls and merges returned children
  beneath the selected root in the Call Hierarchy panel, and selected call rows
  expose direct incoming/outgoing request shortcuts. Remaining polish is
  multi-level mixed incoming/outgoing branch composition.
- Semantic tokens, inlay hints, code lens, and resolved code lens results now
  hydrate async LSP responses into the shared TUI/GUI LSP results panel.
  Semantic tokens apply to buffer state, GUI source rendering emits
  `semantic-token-*` spans, TUI rendering applies config-theme ANSI token
  styles with horizontal-scroll coverage, and edit-time invalidation is covered.
  Inlay hints apply to buffer state, render inline in TUI and headless output,
  render as styled clickable GUI spans, move the cursor to the hint anchor on
  GUI click, clear on edit, and re-request when hints or the inlay panel are
  active. Code lens rows preserve command metadata, apply to buffer state,
  render inline in TUI/GUI/headless output, clear on edit,
  support GUI inline command execution, preserve single and multi-string command
  arguments, preserve structured object/array/primitive command arguments as
  raw JSON payload segments, show argument summaries in result rows before
  execution, expose GUI `data-args`/title metadata, and `code-lens-run`
  dispatches the selected lens command; semantic server legend/modifier naming,
  inlay hint debounce/cancellation, and richer command-specific argument form
  widgets remain.
- Hover now hydrates async `textDocument/hover` responses into the shared
  TUI/GUI LSP results panel, updates a source-position hover popup model, and
  renders escaped GUI hover popup markup. TUI rendering now overlays a styled
  hover popup with behavior coverage. Normal-mode `K` now triggers hover through
  the active LSP and is present in the default keybinding registry. GUI source
  rows now emit `editor-hover` metadata, GUI hover events move the cursor and
  request LSP hover, and repeated GUI hover over the already-visible popup
  position is debounced. Active GUI source characters now expose per-column
  hover targets; configurable hover delay and extending per-column targets to
  all decorated line render modes remain.
- File watching now has controller ownership: activated documents are registered
  with the poll-based watcher and non-broad parent directories are snapshotted.
  TUI/GUI frame loops poll for external changes without clobbering unchanged
  status, changed files refresh matching open buffers from disk, create/change/
  delete events are detected from file hashes plus directory snapshots, noisy
  `.git`, `node_modules`, and `.simple-vault-search.cache` paths are ignored,
  and the watched-file notification path updates vault-search invalidation plus
  active LSP clients with behavior coverage. Remaining work is configurable
  debounce/ignore-glob policy for large vaults.
- Wiki result panels now support keyboard selection and selected-row jump, and
  quick switch can open a TUI/GUI right-dock result panel for loaded notes with
  fuzzy-ranked query matching; GUI wiki panel rows now carry hit-test metadata
  and `wiki-panel-click` opens the clicked target. Richer picker UI and vault
  invalidation remain.
- Debug launch configurations now resolve VSCode-style `${workspaceFolder}`,
  `${file}`, `${fileDirname}`, and `${fileBasename}` variables before session
  start across program, cwd, args, `preLaunchTask`, and string-valued `env`.
  `debug-configs` now opens a command/palette-routed right-dock picker of
  matching VSCode launch configurations, and selecting a row starts that
  configuration. Full VSCode compound support and actual task/env handoff to
  the runtime adapter remain.
- Debug restart now has `debug-restart` command/palette routing and model plus
  controller coverage for moving the active session into a restarting lifecycle
  state. Restart now reopens the editor-side DAP client buffer and queues fresh
  `initialize`/`launch` frames; runtime-backed restart and richer lifecycle UI
  remain.
- Debug lifecycle controls now expose continue, pause, step-over, step-into,
  step-out, terminate, and exception filter commands through command/palette
  routing with controller coverage. Those controls now queue DAP client request
  frames when the adapter buffer is running, terminate stops the client buffer,
  and configured exception filters now render in the Debug Session panel;
  runtime DAP/interpreter backing remains.
- `debug-process-start` now explicitly starts the contributed debug adapter
  (`bin/simple run src/app/dap/simple_dap_main.spl`) through the native
  `rt_process_spawn_piped`/stdin/stdout transport hooks, sends framed
  `initialize` and `launch` requests, and uses the same DAP client request queue.
  The core C runtime bundle now links `runtime_process.c`, and
  `src/app/editor/debug_process_smoke.spl` native-builds and passes against the
  live Simple DAP adapter. The interpreter test runner still does not register
  `rt_process_spawn_piped`, so interpreter coverage stays static/process-shape;
  full native editor-command smoke remains.
- Debug watch/evaluate controls now expose `debug-watch` and `debug-evaluate`
  command/palette routing with controller coverage. The debug model and
  controller now expose result-hydration hooks for watches/evaluate responses,
  and the `debug-console` right-dock Debug Session panel renders watch values
  plus console rows; DAP-backed automatic refresh/runtime REPL execution remains.
- Debug stack/scopes state now has first-class model structs and controller
  hydration hooks. The Debug Session panel renders stack frames, scopes, and
  variables with behavior coverage; command/palette routes can now queue DAP
  `stackTrace`/`scopes`/`variables` requests through the editor-side DAP client.
  Live values remain blocked on interpreter debug hooks.
- The editor debug model now builds DAP `stackTrace`, `scopes`, `variables`,
  and `evaluate` request JSON and parses DAP stack/scope/variable response
  bodies. The controller can hydrate those DAP responses into the Debug Session
  panel, including DAP stack frame source/name/line/column locations. An
  `EditorDebugDapClient` now buffers framed outbound requests, tracks pending
  request sequence IDs, can write frames to a native stdio child process, parses
  Content-Length framed process stdout back into inbound JSON, polls injected or
  process-backed response/event JSON, and removes completed pending requests.
  TUI and GUI frame loops now call silent DAP polling. Remaining debug parity is
  native editor-command smoke coverage plus true runtime stack binding and live
  interpreter-backed values.
- Multi-session debug now has a command/palette-routed `debug-sessions` panel,
  Enter-to-switch behavior, and direct `debug-switch <id>` routing. The active
  session still uses the existing registry-first-session convention; DAP process
  lifecycle binding remains.
- DAP lifecycle events now parse through the debug service and hydrate the
  controller: `stopped` maps to paused, `continued` to running, and
  `terminated`/`exited` to terminated, updating the Debug Session panel with
  behavior coverage. The remaining gap is wiring those event messages from a
  live adapter process into the frame loop.
- The source-backed Simple DAP adapter now advances `current_line` for `next`,
  `stepIn`, and `stepOut`; the live smoke asserts `next` changes subsequent
  `stackTrace` output from line 1 to line 2. This is source-backed stepping,
  not full interpreter execution stepping.
- Breakpoint handling is now less stub-like in the source-backed DAP adapter:
  invalid lines are not retained, `continue` emits a continued event, stops at
  the next verified breakpoint with `reason: breakpoint`, and reports the new
  stack line before a later continue terminates when no breakpoint remains.
- The debug model now builds DAP control requests for continue, pause, step
  (`next`, `stepIn`, `stepOut`), setBreakpoints with condition/log/hit metadata,
  and setExceptionBreakpoints. These are covered at the model layer and are now
  queued by controller actions through the editor-side DAP client; the remaining
  gap is dispatching them through a managed adapter process.
- DAP `evaluate` responses now parse result text and hydrate into the editor
  Debug Session panel as `evaluate-result` console rows. Editor evaluate actions
  now also queue DAP `evaluate` frames when the client buffer is running. The
  remaining REPL gap is sending live evaluate requests through a managed adapter
  process and correlating responses to the original expression.
- Diagnostics now have a command/palette-routed Problems panel in the right dock
  for TUI and GUI, including normal-mode row selection and jump-to-diagnostic
  behavior from the editor diagnostic store. Active-file diagnostics are cleared
  on text changes before requesting fresh LSP diagnostics so the panel does not
  keep stale entries for edited files. TUI single-pane, TUI split-pane, and GUI
  source render paths now show severity-priority diagnostic gutter markers beside
  line numbers. LSP `publishDiagnostics` notifications now replace diagnostics
  for the published URI, including empty-array clearing through the controller
  Problems panel path, and older versioned publishes are ignored.
  `diagnostics-filter <severity>|<source>` now narrows Problems rows by
  severity/source through command and palette routing; `diagnostics-group
  severity|source` now adds grouped Problems rows while preserving
  diagnostic-row jump behavior. GUI Problems filter/group controls dispatch
  through those commands. `diagnostics-sort severity|source|path` sorts
  Problems rows through command, palette, and GUI controls. The selected
  Problems filter/group/sort view is now reapplied after diagnostic refreshes.
- Frontmatter properties now have a command/palette-routed right-dock wiki panel
  for TUI and GUI, backed by the existing Markdown wiki property index with
  controller and index-panel behavior coverage. Active-note frontmatter can also
  be edited through the command/palette-routed `wiki-property-set` action, which
  updates the buffer, preview, LSP state, and property panel. GUI property panels
  now render editable key/value form controls and submit edits through the same
  property command. Vault roots now support `wiki-vault-property-set` bulk
  property updates with open-buffer refresh and a refreshed property panel;
  root-aware GUI property panels expose apply-to-vault controls that route
  through the same bulk command. Richer schema-aware form widgets and safer
  selective bulk-edit review remain.
  Property schema diagnostics now validate required, duplicate, and allowed-value
  frontmatter rules into the existing Problems panel through
  `wiki-property-diagnostics`.
- Markdown HTTP(S) links now hand off to a configured browser command through
  `SIMPLE_EDITOR_BROWSER_COMMAND` or `BROWSER`, falling back to `xdg-open`, with
  controller behavior coverage that avoids launching a real browser in tests;
  richer failure UX remains.
- Markdown vault content search now reuses the syntax-aware Markdown search
  service across vault documents, exposes `editor.wiki_vault_search` through MCP,
  and has a command/palette-routed right-dock search panel with behavior coverage;
  an invalidatable in-memory vault search index now covers refresh/update/remove
  semantics plus watched-change invalidation, controller file-change updates, and
  deterministic relevance ranking with scores surfaced in panels/MCP output, plus
  `.simple-vault-search.cache` save/load reuse from controller and MCP vault
  search paths with persisted-cache freshness checks against current vault
  documents before reuse. Vault search query text now supports `path:` and
  `kind:`/`block:` filters for result narrowing, and the GUI Vault Search panel
  exposes kind filter controls wired through the existing search command.
- GUI Markdown rendering now handles inline `![alt](path)` images inside mixed
  paragraph content as image preview spans while preserving escaped surrounding
  text, in addition to full-line image embed preview blocks.
- Attachment UX now includes an `attachment-picker` command/palette route that
  scans a vault root for attachment/image candidates, filters by query text, and
  displays selectable results in the existing wiki panel. Attachment insertion
  through command/palette and MCP can now copy a source asset into a note-local
  storage folder, choose deterministic suffixed names for storage conflicts,
  and embed the stored relative path; picker rows can insert into a supplied
  target note. Richer picker presentation and variable target controls remain.
- Template rendering now supports caller-provided custom variables in addition
  to `{{title}}` and `{{date}}` through service APIs and MCP preview/insert
  paths; the editor has a command/palette-routed wiki-panel template picker.
  Richer picker filtering and variable form UI remain.
- Daily-note creation now accepts workspace-style folder, title-format, and
  extension options through the service, MCP preview/create paths, and
  command/palette payloads; date picker UI remains.
- Tag result panels now have explicit behavior coverage for selected-row
  navigation to the source file and line; vault invalidation remains.
- LSP result jumps now push the previous file/line/column onto a controller
  location stack, and `lsp-back` restores that location with behavior coverage;
  richer history UI remains.
- Workspace-symbol requests now accept command/palette/MCP query payloads and
  send those through the actual `workspace/symbol` LSP JSON; indexing remains.
- Document-symbol result rows can now update the active Markdown outline state
  with behavior coverage; richer non-Markdown outline UI remains.
- Wiki graph panel rows now resolve linked note targets through the active wiki
  index, so selecting a resolved graph edge navigates to the destination note.
- GUI graph panels now render graph rows as clickable graph-node markup using
  the existing wiki panel click event path.

Known production gaps:

- Obsidian-style Markdown is incomplete: preview/source-backed rendering and
  right-dock wiki result panels exist, but full live visual editing must still
  cover richer TUI table interaction, callout edit preservation/richer styling,
  richer task query UI, schema-aware property widgets/safer selective bulk-edit review, spatial graph layout,
  navigation, richer vault search path/query-builder polish, richer template picker filtering and variable form UI, richer attachment picker presentation/target controls, and stable cursor/selection behavior
  while rendered.
- VSCode-style key UX now includes default `Ctrl+Space`, `F12`, `Ctrl+.`, and
  `F5` shortcuts plus a launch configuration picker and `keyboard-shortcuts`
  discovery panel; richer GUI picker presentation remains.
- LSP is incomplete as a production editor surface: completion/hover/definition/
  code-action requests, navigation result panels, and a Problems panel exist,
  plus TUI/GUI gutter diagnostics, GUI hover popup markup/dismissal, rename preview/confirm,
  and async navigation/formatting result hydration, but richer diagnostics table polish,
  richer rename diff/conflict UI, hover delay/decorated-line UX, formatting richer review UI, semantic-token theme
  mapping/TUI styling, inlay hint refresh policy, signature-help overload navigation,
  richer code-lens command-specific argument form widgets, multi-level mixed
  call hierarchy branch composition, and configurable watcher debounce/ignore-glob
  policy remain parity work.
- DAP is not production-level: the current adapter remains source-backed. A repo
  search found `src/app/dap/hooks.spl`, but no connected interpreter debug hook
  implementation in interpreter paths. True runtime breakpoints, stepping, call
  stack/scopes/variables request binding, automatic watch refresh, runtime evaluation, exception handling, runtime restart,
  terminate, and breakpoint lifecycle are follow-up architecture/implementation
  tasks.
- MCP/editor automation had a registered `editor.goto_definition` tool without a
  dispatcher path before this update.

Verification evidence collected in this session:

```bash
bin/simple check src/app/editor src/lib/editor src/app/md_lsp src/app/dap test/system/editor_controller_spec.spl test/system/editor_extension_spec.spl test/system/editor_lsp_spec.spl test/system/editor_md_lsp_code_action_spec.spl test/system/editor_markdown_spec.spl test/system/dap_protocol_live_spec.spl test/system/simple_lsp_protocol_live_spec.spl
python3 scripts/smoke/dap_protocol_smoke.py
python3 scripts/smoke/simple_lsp_protocol_smoke.py
bin/simple test test/system/editor_controller_spec.spl --mode=interpreter
bin/simple test test/system/editor_extension_spec.spl --mode=interpreter
bin/simple test test/system/editor_lsp_spec.spl --mode=interpreter
bin/simple test test/system/editor_md_lsp_code_action_spec.spl --mode=interpreter
bin/simple test test/system/editor_markdown_spec.spl --mode=interpreter
bin/simple test test/system/dap_protocol_live_spec.spl --mode=interpreter
bin/simple test test/system/simple_lsp_protocol_live_spec.spl --mode=interpreter
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
bin/simple test test/system/editor_buffer_spec.spl --mode=interpreter --fail-fast
bin/simple test test/system/editor_wal_spec.spl --mode=interpreter --fail-fast
bin/simple test test/system/editor_gui_spec.spl --mode=interpreter --fail-fast
bin/simple test test/system/editor_controller_spec.spl --mode=interpreter --fail-fast
bin/simple check src/app/editor src/lib/editor src/lib/common/markdown test/system/editor_buffer_spec.spl test/system/editor_controller_spec.spl test/system/editor_gui_spec.spl test/system/editor_markdown_spec.spl test/system/editor_md_wiki_index_spec.spl test/system/editor_debug_session_spec.spl test/system/editor_keybinding_spec.spl test/system/editor_gui_sdl_spec.spl test/system/editor_lsp_spec.spl test/system/editor_lsp_transport_spec.spl test/system/editor_wal_spec.spl
```

## Production Completion Work Plan

Completion requires the audit checklist below to pass with behavior tests, not
only source-presence assertions. The current feature matrix lives in
`doc/03_plan/editor_ide_production_matrix_2026-05-13.md`.

### 0. Production Feature Matrix

Status: IN PROGRESS.

Maintain a concrete checklist for:

- Obsidian/wiki parity: visual Markdown editing, wiki links, backlinks,
  unresolved links, embeds, callouts, tasks, tags, properties/frontmatter, graph,
  outline, quick switcher, vault search, templates, daily notes, attachments,
  command palette, and plugin extension points.
- VSCode debug parity: launch configs, breakpoints, conditional/log breakpoints,
  hit counts, stepping, pause/continue, restart, stop, stack frames, scopes,
  variables, watches, REPL/evaluate, debug console, exception breakpoints, source
  maps/paths, multiple sessions, and UI state.
- LSP parity: completion, hover, go-to definition, declaration, implementation,
  type definition, references, rename, code actions, diagnostics, document
  symbols, workspace symbols, formatting, range formatting, semantic tokens,
  inlay hints, signature help, folding ranges, selection ranges, document links,
  code lens, call hierarchy, workspace folders, file watching, and indexing/cache
  invalidation.

Stop condition: every row has an owner file, behavior test, and pass/fail status.

### 1. VSCode Shortcut And Command Parity

Status: PARTIAL. `Ctrl+Space`, `F12`, `Ctrl+.`, and `F5` are now routed through
normal-mode and GUI paths, default keybinding entries exist, and `F12` opens the
LSP result panel for definition locations.

Remaining:

- Add mouse `Ctrl+Click` definition routing where GUI event data exposes
  modifier state and hit testing. Link Ctrl+Click and shortcut discovery are
  covered.
- Polish GUI picker presentation for launch configuration selection.

Stop condition: keybinding tests and GUI event tests prove the shortcuts dispatch
to LSP, quick-fix, and DAP surfaces.

### 2. MCP Navigation And Automation Parity

Status: PARTIAL. `editor.goto_definition` now dispatches through the active LSP
definition request, and `editor.run_command` routes controller-level commands
instead of buffer-only commands.

Remaining:

- Add remaining MCP tools for debug session control and richer structured
  diagnostics/code-action results; references, LSP symbols/rename, Markdown
  backlinks, and open-note/disk-backed wiki search/query surfaces now exist.
- Return structured locations instead of raw response JSON.

Stop condition: behavior specs exercise each registered tool end-to-end.

### 1. Re-audit Current Files

Status: FOUNDATION VERIFIED in the 2026-05-13 restart session.

Confirm the new files and patched surfaces still exist:

```bash
ls src/app/dap/simple_dap_main.spl scripts/smoke/dap_protocol_smoke.py test/system/dap_protocol_live_spec.spl
rg -n "ExtensionDebugAdapter|find_debug_adapter|codeActionProvider|simple_lsp_config|quickfix|debug-start" src/app src/lib test/system --glob '*.spl'
```

Stop condition: the restored DAP, extension, quick-fix, and LSP config surfaces
are present and match the verified state above.

### 2. Tighten Quick-Fix Application

Status: FOUNDATION VERIFIED in the 2026-05-13 restart session.

Current quick-fix support requests and stores actions, but application is still
shallow. Implement real application of `EditorCodeAction.edit_json` to the active
buffer.

Expected behavior:

- `quickfix` populates `EditorController.code_actions`.
- `quickfix-apply` mutates the active buffer for the selected action.
- Markdown heading spacing, empty link, and trailing whitespace fixes are covered.
- Tests assert behavior, not only source-text presence.

### 3. Wire Real LSP Lifecycle Into Editor Open/Edit

Status: FOUNDATION VERIFIED in the 2026-05-13 restart session.

Markdown and Simple LSP config wrappers exist, but editor lifecycle wiring is
incomplete.

Implement or verify:

- LSP starts when opening `.md`, `.markdown`, `.spl`, or `.shs` files.
- `didOpen` and `didChange` fire from editor document lifecycle.
- Diagnostics notifications populate `DiagnosticStore`.
- Completion, hover, definition, and code actions use the active language server.

Keep request handlers hot-path safe: no repeated full-tree scans or shell-outs in
cursor-move/completion/diagnostic paths.

### 4. Upgrade Simple LSP Surface

Status: FOUNDATION VERIFIED in the 2026-05-13 restart session.

`simple_lsp_config.spl` currently points at `bin/simple lsp`. Verify the command
exists and is the intended Simple LSP server surface. If the actual server is
`src/app/simple_lsp_mcp`, decide whether the editor needs LSP protocol or MCP
tool protocol and adjust the config accordingly.

Required proof:

- A live smoke for Simple completion/definition/codeAction, equivalent in spirit
  to the DAP smoke.
- A system spec wrapping that smoke.

### 5. DAP Integration Beyond Protocol Smoke

Status: FOUNDATION ONLY in the 2026-05-13 restart session. The adapter
now has broader live protocol and negative coverage, including source path and
breakpoint-line behavior against real `.spl` source files. True interpreter
debug-hook stepping is not marked complete because the repo currently exposes
only the `src/app/dap/hooks.spl` abstraction plus FFI declarations/stubs, with no
connected interpreter implementation found under the interpreter paths.

The restored adapter is a protocol-valid smoke adapter, not a full interpreter
debugger.

Remaining DAP work:

- Connect launch/step/continue/breakpoints to real interpreter hooks where
  possible.
- `F5` now defaults to `debug-process-start` so the primary debug shortcut uses
  the process-backed DAP transport. The lower-level native process-pipe DAP
  launch smoke and the full native editor command smoke now both pass. The
  command path starts the Simple adapter, sends `initialize`/`launch`, observes
  the stopped event, updates controller status to `paused`, and terminates the
  child adapter. The implementation uses native runtime shims for the Simple DAP
  spawn/start/wait path because the full editor native closure currently
  corrupts text arguments/returns across the generic process extern boundary.
  Remaining production work is to replace that shim with the generic DAP client
  path after the native text extern issue is fixed, then extend restart/session
  lifecycle coverage.
- Focused regression note resolved for this slice:
  `src/compiler_rust/target/debug/simple test
  test/system/editor_controller_spec.spl --mode=interpreter --fail-fast`
  now passes with 71 examples and 0 failures. The earlier file-watcher hash
  overflow was fixed, and the controller now uses stable DAP helper functions
  for initialize/launch, breakpoint sync, controls, inject, and poll state so
  queued frames and pending requests survive immutable client updates.
- Keep legacy `test/system/dap/dap_stepping_system_spec.spl` in mind: it was
  previously hang-prone, so run it only under a timeout guard.

### 6. Markdown Inline Visual Editing Audit

Status: FOUNDATION ONLY for the source-backed renderer/editor surfaces in the
2026-05-13 restart session. Full pixel/interactive GUI audit remains outside this
headless plan slice.

Audit and finish the Obsidian-like Markdown editing surface:

- Inline rendered headings, emphasis, links, code spans, lists, tables, and tasks.
- Source remains editable without losing Markdown syntax fidelity.
- Cursor movement, selection, undo/redo, and save behavior stay stable.
- TUI and GUI paths render code-action popups without overlap.

### 7. Verification Gates

Status: FOUNDATION VERIFIED for the restart slice in the 2026-05-13 session.

Run narrow gates after each slice, then a broader editor gate:

```bash
bin/simple check src/app/editor src/lib/editor src/app/md_lsp src/app/dap test/system/editor_controller_spec.spl test/system/editor_extension_spec.spl test/system/editor_lsp_spec.spl test/system/editor_md_lsp_code_action_spec.spl test/system/dap_protocol_live_spec.spl
python3 scripts/smoke/dap_protocol_smoke.py
bin/simple test test/system/editor_controller_spec.spl --mode=interpreter
bin/simple test test/system/editor_extension_spec.spl --mode=interpreter
bin/simple test test/system/editor_lsp_spec.spl --mode=interpreter
bin/simple test test/system/editor_md_lsp_code_action_spec.spl --mode=interpreter
bin/simple test test/system/dap_protocol_live_spec.spl --mode=interpreter
```

For compiler/core/lib, MCP, LSP, or packaging-impacting changes, also run the
AGENTS.md required smoke checks for `src/compiler`, `src/lib`, `src/app/mcp`,
and `src/app/simple_lsp_mcp`.

## Suggested Restart Prompt

Use this in a new session:

```text
Continue the Simple editor IDE work from doc/03_plan/editor_ide_restart_plan_2026-05-13.md. First re-audit the current files and dirty worktree without reverting unrelated changes. Then implement the remaining editor quick-fix application, real Markdown/Simple LSP lifecycle wiring, and DAP integration improvements, validating each slice with the commands in the plan. Do not mark the overall goal complete until the full editor/DAP/LSP/Markdown audit passes.
```
