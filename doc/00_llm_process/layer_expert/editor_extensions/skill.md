# Layer Expert: editor_extensions

Owns the IDE extension kernel layer and the document service beneath it.
Landed v1 2026-07-29 (ledger:
`doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`
§Execution status). Feature view:
[feature_expert/ide_extension_kernel](../../feature_expert/ide_extension_kernel/skill.md).

## Owned source

- `src/lib/editor/extensions/` — `contract.spl` (ids, SemVer ranges,
  descriptors), `manifest.spl` (typed model), `manifest_sdn.spl` (SDN decode +
  diagnostics), `api.spl` (Disposable, ExtensionLifetime, CancellationToken —
  `ContextKeys`/`WhenPredicate`/`when_eval` were deleted 2026-07-30, see
  Known gaps), `registry.spl` (CommandRegistry, EventListenerRegistry,
  LanguageIndex), `host.spl` (activation router, dispatch, lifecycle,
  keybinding-contribution sink), `runtime.spl` (path containment, permissions,
  crash containment), `builtin/` (14 manifest providers + activation hooks).
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
`test/01_unit/lib/editor/keybinding_contribution_spec.spl` (contributed
keybindings round-trip through the host's `KeybindingManager` on
activate/deactivate — does not prove editor dispatch reads it, see Known
gaps), `test/01_unit/lib/editor/document_service_spec.spl`,
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
- **CRITICAL — `bound` in `ide_capabilities_live()` is a self-fulfilling probe,
  not evidence anything works.** `src/app/ide/capabilities.spl:213-215`
  registers a probe command handler and then checks whether that same handler
  is registered — a write-then-check-your-own-write. It proves a command id
  *can* be bound through the real `CommandRegistry` (the code's own line-169
  comment says exactly that); it is not evidence any real caller invokes the
  command or that a real handler backs it. This stacks with eager builtin
  activation (next bullet): together they make a builtin-backed capability
  nearly guaranteed to report `bound` regardless of merit. Sheets case study:
  adding `ExtensionLanguage(id: "sheets", extensions: [".xlsx",".xls",".csv"])`
  to `builtin/sheets_ext.spl` flips the census from 10-of-11 to 11-of-11 bound
  purely because the extension strings substring-match compat tags in
  `_ide_manifest_matches_tag` — `sheets-function-registry-demo` itself is
  still one of the two lazily-UNREACHABLE builtins (its only activation event,
  `onFunctionRegistry:sheets`, is emitted nowhere in `src/`) and could never
  reach `bound` under genuine lazy activation. Never cite the bound count as
  proof of working end-to-end behavior. Filed:
  `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md` §
  CRITICAL.
- **Builtins activate eagerly** at `extension_host_with_builtins()` (host.spl:712),
  so `activate_language`/`activate_command` return 0 for them and every builtin
  capability reports `bound`. Laziness holds only for the discovered path.
  Filed: `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md`.
- **`api.spl`'s `ContextKeys` / `WhenPredicate` / `when_eval` were deleted
  2026-07-30** (verified 0 external consumers against `origin/main`) — they
  were used only by the already-deleted `settings.spl`/`menus.spl`/
  `keybindings.spl` registries.
- **`contributes_keybindings` is now bound into a host-owned `KeybindingManager`
  but has no reader.** `host.spl` `_register_contributions` feeds each
  contribution through `keybinding_manager_add_override` (reversed on
  deactivate by `_rebuild_keybinding_overrides`; queried via
  `keybinding_resolve(key, mode)`). That `KeybindingManager` instance appears
  nowhere else in the repo — `editor_controller.spl` uses a different stack
  (`std.editor.common.keybindings.default_keybindings()`) only to render the
  shortcuts panel, with no key→command resolution through the host's manager.
  A contributed keybinding still cannot reach dispatch; it moved from "parsed
  and dropped" to "parsed and stored where nothing reads it". The `when`
  predicate is dropped in the conversion (`KeyBinding` has no such field).
  Spec: `test/01_unit/lib/editor/keybinding_contribution_spec.spl`, 6/6 (proves
  the sink round-trips, not that dispatch works).
- `contributes_themes` still decodes with nothing binding it — parsed and
  dropped, unchanged. `contributes_custom_editors` is declared by three
  builtins (`writer.rich_document_editor`, `sheets.grid`, `slides.canvas`) and
  routed by none; another lane is binding this now — treat as in progress, not
  fixed, until confirmed.
