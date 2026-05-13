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
- `scripts/dap_protocol_smoke.py` exists and drives initialize, launch, breakpoints,
  stack, scopes, variables, evaluate, and disconnect.
- `test/system/dap_protocol_live_spec.spl` exists and wraps the live smoke.
- Extension manifests now support `ExtensionDebugAdapter`.
- `simple-language` contributes the `simple` debug adapter:
  `src/app/dap/simple_dap_main.spl`.
- `ExtensionHost` registers and looks up debug adapters.
- LSP client/transport now have `textDocument/codeAction` request support.
- Markdown LSP advertises `codeActionProvider` and returns simple quick-fix actions.
- Editor controller has quick-fix/debug-start command routing and state fields.
- `src/lib/editor/60.services/simple_lsp_config.spl` was added as the Simple LSP config surface.

Verified commands that passed before this handoff:

```bash
bin/simple check src/lib/editor/50.extensions/manifest.spl src/lib/editor/50.extensions/host.spl src/lib/editor/50.extensions/builtin/spl_language.spl src/lib/editor/50.extensions/builtin/md_language.spl test/system/editor_extension_spec.spl src/app/dap/simple_dap_main.spl test/system/dap_protocol_live_spec.spl
python3 scripts/dap_protocol_smoke.py
bin/simple test test/system/dap_protocol_live_spec.spl --mode=interpreter
bin/simple test test/system/editor_extension_spec.spl --mode=interpreter
bin/simple check src/lib/editor/60.services/lsp_transport.spl src/lib/editor/60.services/lsp_client.spl src/lib/editor/60.services/md_lsp_config.spl src/lib/editor/60.services/simple_lsp_config.spl src/lib/editor/60.services/diagnostics.spl src/app/md_lsp/md_lsp_handler.spl src/app/editor/commands.spl src/app/editor/editor_controller.spl
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
- `src/lib/editor/50.extensions/builtin/md_language.spl`
- `src/lib/editor/50.extensions/builtin/spl_language.spl`
- `src/lib/editor/50.extensions/host.spl`
- `src/lib/editor/50.extensions/manifest.spl`
- `src/lib/editor/60.services/diagnostics.spl`
- `src/lib/editor/60.services/lsp_client.spl`
- `src/lib/editor/60.services/lsp_transport.spl`
- `src/lib/editor/60.services/md_lsp_config.spl`
- `src/lib/editor/60.services/simple_lsp_config.spl`
- `test/system/editor_controller_spec.spl`
- `test/system/editor_extension_spec.spl`
- `test/system/editor_lsp_spec.spl`
- `test/system/editor_md_lsp_code_action_spec.spl`

Before continuing, run `git status --short --untracked-files=all` and verify the
DAP files still exist. During the previous session, some untracked files
disappeared between operations.

## Remaining Work Plan

### 1. Re-audit Current Files

Confirm the new files and patched surfaces still exist:

```bash
ls src/app/dap/simple_dap_main.spl scripts/dap_protocol_smoke.py test/system/dap_protocol_live_spec.spl
rg -n "ExtensionDebugAdapter|find_debug_adapter|codeActionProvider|simple_lsp_config|quickfix|debug-start" src/app src/lib test/system --glob '*.spl'
```

Stop condition: the restored DAP, extension, quick-fix, and LSP config surfaces
are present and match the verified state above.

### 2. Tighten Quick-Fix Application

Current quick-fix support requests and stores actions, but application is still
shallow. Implement real application of `EditorCodeAction.edit_json` to the active
buffer.

Expected behavior:

- `quickfix` populates `EditorController.code_actions`.
- `quickfix-apply` mutates the active buffer for the selected action.
- Markdown heading spacing, empty link, and trailing whitespace fixes are covered.
- Tests assert behavior, not only source-text presence.

### 3. Wire Real LSP Lifecycle Into Editor Open/Edit

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

`simple_lsp_config.spl` currently points at `bin/simple lsp`. Verify the command
exists and is the intended Simple LSP server surface. If the actual server is
`src/app/simple_lsp_mcp`, decide whether the editor needs LSP protocol or MCP
tool protocol and adjust the config accordingly.

Required proof:

- A live smoke for Simple completion/definition/codeAction, equivalent in spirit
  to the DAP smoke.
- A system spec wrapping that smoke.

### 5. DAP Integration Beyond Protocol Smoke

The restored adapter is a protocol-valid smoke adapter, not a full interpreter
debugger.

Remaining DAP work:

- Connect launch/step/continue/breakpoints to real interpreter hooks where
  possible.
- Verify breakpoint hit line and stack frame source path against a real `.spl`.
- Add negative tests for missing program, invalid breakpoints, and evaluation of
  unavailable variables.
- Keep legacy `test/system/dap/dap_stepping_system_spec.spl` in mind: it was
  previously hang-prone, so run it only under a timeout guard.

### 6. Markdown Inline Visual Editing Audit

Audit and finish the Obsidian-like Markdown editing surface:

- Inline rendered headings, emphasis, links, code spans, lists, tables, and tasks.
- Source remains editable without losing Markdown syntax fidelity.
- Cursor movement, selection, undo/redo, and save behavior stay stable.
- TUI and GUI paths render code-action popups without overlap.

### 7. Verification Gates

Run narrow gates after each slice, then a broader editor gate:

```bash
bin/simple check src/app/editor src/lib/editor src/app/md_lsp src/app/dap test/system/editor_controller_spec.spl test/system/editor_extension_spec.spl test/system/editor_lsp_spec.spl test/system/editor_md_lsp_code_action_spec.spl test/system/dap_protocol_live_spec.spl
python3 scripts/dap_protocol_smoke.py
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
