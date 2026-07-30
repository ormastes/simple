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
anti-pattern must not return. It was **not** fully removed on the first pass:
`extension_discovery_contract_spec.spl` still had 10 `read_text(...).contains(...)`
assertions until 2026-07-30, and an untracked
`.spipe_matchers_extension_discovery_contract_spec.spl` sitting beside it still
does. Re-grep for `.contains("fn \|.contains("me ` before trusting this line.

## Known gaps (do not re-discover)

Typed language-provider registration (providers currently tunnel through
commands), SDN-typed dispatch payloads, `onLanguage:` activation for provider
dispatch, hot-path dispatch cost (linear scan + event-log per call — keep
per-keystroke assists direct), worker/WASM out-of-process host, symlink
resolution on Windows.

Measured 2026-07-30, do not re-derive:
- **Builtins activate eagerly** at `extension_host_with_builtins()` (host.spl:712),
  so `activate_language`/`activate_command` return 0 for them and every builtin
  capability reports `bound`. Laziness holds only for the discovered path.
  Filed: `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md`.
- **`settings.spl` / `menus.spl` / `keybindings.spl` were DELETED** 2026-07-30 —
  zero importers, and each duplicated a live stack: settings →
  `lib/editor/00.common/settings_schema.spl` + `view/settings_view.spl`
  (consumed by `editor_ctrl_core.spl`, both shells); keybindings →
  `lib/editor/00.common/keybindings.spl` + `core/keybinding_manager.spl`
  (consumed by `editor_controller.spl`); menus had **neither** end — there is no
  `contributes_menus` field, so an extension cannot contribute a menu at all.
  Do not recreate them; extend the live stacks.
- `api.spl`'s `ContextKeys` / `WhenPredicate` / `when_eval` were used only by
  those registries and are now unreferenced — sweep or cover them.
- Manifest `keybindings` and `themes` decode but nothing binds them;
  `custom_editors` are declared by three builtins and routed by none. The right
  fix for keybindings is feeding them to `keybinding_manager_add_override`, not
  a parallel registry.
