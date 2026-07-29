# Layer Expert: editor_extensions

Owns the IDE extension kernel layer and the document service beneath it.
Landed v1 2026-07-29 (ledger:
`doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`
§Execution status). Feature view:
[feature_expert/ide_extension_kernel](../../feature_expert/ide_extension_kernel/skill.md).

## Owned source

- `src/lib/editor/extensions/` — `contract.spl` (ids, SemVer ranges,
  descriptors), `manifest.spl` (typed model), `manifest_sdn.spl` (SDN decode +
  diagnostics), `api.spl` (Disposable, ExtensionLifetime, CancellationToken,
  WhenPredicate), `registry.spl` (CommandRegistry, EventListenerRegistry,
  LanguageIndex), `host.spl` (activation router, dispatch, lifecycle),
  `runtime.spl` (path containment, permissions, crash containment),
  `settings.spl` / `menus.spl` / `keybindings.spl` (Wave-2 registries),
  `builtin/` (14 manifest providers + activation hooks).
- `src/lib/editor/document/` — `model.spl`, `transaction.spl`, `registry.spl`
  (handles, views, autosave, hot exit), `traits.spl` (DocumentCodec /
  DocumentEditorProvider / DocumentRenderer).

## Public contract (stable — change via a plan, not in passing)

`extension_manifest_load[_with_diagnostics]`, `extension_manifest_decode`,
`ExtensionHost.{register_command_handler, register_activation_hook,
dispatch_command, on_event, emit_event, activate*, deactivate}`,
`CommandRegistry.register(owner, id, title, fn) -> Disposable`,
`DocumentRegistry.{open, apply, undo, register_view, autosave_pending,
serialize_state, restore_state}`, `DocumentCodec`.

Consumers depending on these today: `src/app/editor/` (controller + GUI shell),
`src/app/office/{word,sheets,slides}`, `src/app/ide/capabilities.spl`,
`src/app/vscode_extension/`.

## Boundaries

- **Kernel never imports app code.** Builtin manifests under `builtin/` are the
  seam; `sheets_ext.spl`/`slides_ext.spl` currently import
  `app.office.sheets|slides` — an inverted lib→app edge accepted because the
  office domains still live under `src/app/`. Fix direction: move the domains,
  not the seam.
- **Separate from the native plugin registry** (`src/app/plugin/registry.spl`,
  SFFI libraries/symbols). They share only the SDN decoder and id/version
  utilities — do not merge them.
- Themes come from `ResolvedThemePackage`/`ThemeRenderSnapshot`; the kernel
  carries no theme engine (the 43-LOC duplicate was deleted 2026-07-29).

## Tests

`test/01_unit/lib/editor/extensions/*.spl` (manifest_sdn, registry, lifecycle,
runtime_security, activation_hook, settings, menus, keybindings),
`test/01_unit/lib/editor/document_service_spec.spl`,
`test/03_system/ide/extension_kernel_walking_skeleton_spec.spl` (+ fixture
`test/fixtures/ide_extensions/hello/`),
`test/03_system/ide/markdown_extension_slice_spec.spl`.

Run one spec at a time with `SIMPLE_TIMEOUT_SECONDS=900` (see the SPipe skill's
loaded-box section). No source-text assertions in this layer's specs — that
anti-pattern was removed here and must not return.

## Known gaps (do not re-discover)

Typed language-provider registration (providers currently tunnel through
commands), SDN-typed dispatch payloads, `onLanguage:` activation for provider
dispatch, hot-path dispatch cost (linear scan + event-log per call — keep
per-keystroke assists direct), worker/WASM out-of-process host, symlink
resolution on Windows.
