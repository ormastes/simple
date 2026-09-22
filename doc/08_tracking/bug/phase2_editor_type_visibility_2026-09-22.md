# Phase2 editor type visibility candidate

STATUS: WARN — markdown dispatch native compilation passes; full CLI admission pending.

Base: PR #1207, `25d609723cd37da32c645eb3c95d464243d5fa73`.
Origin main lacks the PR's earlier optional-state and pixel dock-geometry fixes;
those changes are preserved. No open editor PR was found in the scoped query.

The run-3 CLI build reported `gui_shell` text/integer mismatch,
`md_dispatch` ANY.preview_visible, and both language configurations wildcard.ok.
This candidate imports the types at their use sites and annotates the initialize
response with the existing LspResponse return contract. It changes no runtime
control flow, FFI, platform dependency, or SoSIX boundary.

## Evidence

Compiler: fresh Phase2 run-3 snapshot, SHA256
`531b1b9b270a66e5ed30c0c9311f013ad451d0f17377ddb24f01fce4df372e20`.
Its matching immutable stage2 runtime capsule was used with no-stub fallback.
All probes ran in a separate worktree, with separate caches and a process-tree
RSS cap of 5,859,375 KiB. No active suite source or cache was edited.

- Native `md_dispatch.spl` entry, source roots src/lib/editor and src/app/editor:
  **PASS**, 44 compiled, 0 cached, 0 failed; 12.30 seconds;
  process-tree peak 364,960 KiB; watchdog exit 0, quiescent 1.
- Native md_lsp_config entry clears its own reported HIR failure but its
  lsp_client dependency fails on missing transport-config type context
  (`LspClientConfig.server_args`). This is not a passing build.
- Standalone gui_shell entry lacks ambient EditorController context and fails
  earlier on ANY.file_tree_visible. It does not reproduce the full CLI context.
- Full CLI-context native probe: timed out at 240.79 seconds; exit 124,
  process-tree peak 2,646,240 KiB, quiescent 1. No target-file diagnostics were
  emitted before timeout. This is neither success nor evidence of elimination.
- Phase2 snapshot supports compile/native-build only; `test` and `check`
  commands are unavailable. New behavioral spec remains **UNRUN**.
- Working direct-env-runtime guard PASS; diff whitespace check PASS;
  executable specs beneath doc/06_spec: 0.
- Independent review found the imports consistent with their declared types,
  no semantic regression, and no new SoSIX/native dependency. It explicitly
  withheld compile acceptance, especially for optional-state inference.

Local logs: `/Users/ormastes/simple-tmp/phase2-editor-config-20260922/build/phase2-probe/`.
`md.log` is the passing focused build, `config.log` and `editor.log` are the
context-limited failures, `cli.log` is the timeout, `spec.log` records the
unsupported test command, and `tmp/*.env` holds watchdog receipts.

Required next gate: run the regression spec with an admitted full CLI and finish
the integrated CLI build. Do not mark the GUI/config corrections verified or
release this candidate on the source review alone.
