# Authoring an IDE Extension

How to add a Simple IDE extension: a static SDN manifest describes what the
extension contributes, typed Simple code supplies the behavior, and the host
binds them lazily. Landed 2026-07-29 — see
`doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`.

## 1. The manifest (`extension.sdn`)

Schema id `simple.ide.extension/1`. Only data that must be known **without
executing the extension** lives here: identity, activation index,
contributions, permissions, host placement.

```
extension:
    schema: "simple.ide.extension/1"
    id: fixture.hello
    display_name: "Hello"
    version: 1.0.0
    engine: ">=0.2.0 <1.0.0"
    entry: app.ide.extensions.hello
    host: workspace

permissions:
    workspace_read: true
    workspace_write: false
    process_spawn: false
    network_client: false
    secrets: false
    native_ffi: false

activation:
    events: ["onCommand:hello.greet"]

contributes:
    commands: [{id: hello.greet, title: "Hello: Greet", category: Fixture}]
    languages: [{id: markdown, extensions: [".md"]}]
```

Working example: `test/fixtures/ide_extensions/hello/`.

Rules that bite:
- **Quote activation event strings.** Unquoted `onCommand:x` parses as a nested
  mapping.
- Permissions are **default-deny**; an absent key is denied, not inherited.
- Decoding reports *all* problems at once —
  `extension_manifest_load_with_diagnostics(path)` returns
  `{manifest, issues, ok}` with real line/col, including duplicate keys.

## 2. The behavior (typed Simple)

Commands are typed handlers, not strings. Registration returns a `Disposable`
owned by the extension's lifetime, so deactivation removes everything:

```
host.register_command_handler("hello", "hello.greet", "Hello: Greet",
    \payload: Ok("hello:" + payload))
```

Duplicate ids are **first-wins** plus a conflict diagnostic — the second
registration returns a `Disposable` of kind `command-conflict`, and the
original handler keeps serving. Everything (palette, menu, keybinding,
programmatic) dispatches through the same path:

```
host.dispatch_command("hello.greet", payload)   # activates lazily, then runs
```

Work that must happen when an extension activates (registering formula
functions, slide layouts, …) goes in an **activation hook** — it runs exactly
once per activation, and a failing hook becomes a diagnostic plus crash-state,
never a host crash:

> **Builtins are not lazy.** `extension_host_with_builtins()` eagerly activates
> every builtin at construction (`host.spl:712`), so a builtin's hook runs at
> startup regardless of its `activation.events`. Laziness is real only for
> disk-discovered extensions. Filed:
> `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md`.

```
host.register_activation_hook("sheets", sheets_ext_activation_hook)
```

## 3. Editing documents

Never mutate buffers directly. Go through the document service
(`src/lib/editor/document/`): `DocumentRegistry.open/apply/undo`, with
`DocumentTransaction` carrying the edits. Registered views are invalidated with
the post-transaction version, so a source editor and a preview stay consistent.
Persisting a document means implementing `DocumentCodec` (see
`RichDocumentCodec` in Writer and `WorkbookCodec` in Sheets) — a save that only
clears a dirty flag is a bug, not a save.

## 4. Domain registries

Extend a domain instead of forking it:

| Registry | Adds |
|---|---|
| `app/office/sheets/function_registry.spl` | formula functions (`DOUBLE(n)`) |
| `app/office/slides/layout_registry.spl` | slide layouts + placeholders |
| `app/office/slides/element_kind_registry.spl` | slide element kinds |

Settings do **not** go through the extension kernel. Use the live stack:
`lib/editor/00.common/settings_schema.spl` →
`lib/editor/view/settings_view.spl`. Kernel-side `settings.spl` / `menus.spl` /
`keybindings.spl` were deleted 2026-07-30 as unused duplicates of the live
stacks. There is no menu contribution point: `ExtensionManifest` has no
`contributes_menus` field.

Manifest `keybindings` **are now bound into a host-owned `KeybindingManager`**
(`host.spl` `_register_contributions` → `keybinding_manager_add_override`,
reversed by `_unregister_contributions` on deactivate; query via
`host.keybinding_resolve(key, mode)`). But nothing in the running editor reads
that manager: `editor_controller.spl` only calls `default_keybindings()` (from
`lib/editor/00.common/keybindings.spl`, a separate stack) to render the
keyboard-shortcuts panel — there is no key→command resolution path through the
host's `KeybindingManager` anywhere. So a contributed keybinding still cannot
reach dispatch; it is stored, not wired. The `when` context-predicate field on
a keybinding contribution is also dropped in the conversion — `KeyBinding` has
no "when" concept. Spec:
`test/01_unit/lib/editor/keybinding_contribution_spec.spl` (6/6, proves the
sink round-trips, not that dispatch works). Details:
`doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md` §
Adjacent, not fixed here.

## 5. Shipping a builtin

Add `src/lib/editor/extensions/builtin/<name>_ext.spl` returning a typed
manifest, then exactly one provider line in `builtin/index.spl`. Declare only
commands that have a real implementation behind them — `ide_capabilities_live()`
reports `declared → indexed → activatable → bound`, and a command with no
handler stops at `activatable`, visibly.

> **`bound` requires a real handler — and no builtin registers one yet.**
> `_ide_capability_with_live_state` (`src/app/ide/capabilities.spl`) used to
> register its own probe command handler and then check whether that same
> handler was registered — a write-then-check-your-own-write that made
> `bound` unfalsifiable (fixed 2026-07-31, see
> `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md` §
> CRITICAL). It now only reads `host.command_handler_registered(command_id)`
> — a real check. Today that check is false for every builtin: none of them
> register a `CommandRegistry` handler on the host `ide_capabilities_live()`
> builds (the five markdown handlers in `editor_controller.spl` are
> registered on a *different*, app-owned host). So every builtin-backed
> capability's honest ceiling is `activatable`, not `bound`, until a builtin
> actually wires a real handler through `register_command_handler`. Do not
> treat "`declared → activatable → bound`" progressing to `bound` as proof
> the feature works end to end even once one does — `bound` only proves the
> command id resolves to *a* handler, not that it is correct.

## 6. Security model

Third-party extensions are untrusted. `runtime.spl` canonicalizes paths
(resolving symlinks via `rt_path_absolute`) before containment checks, so
`/root-evil` is not inside `/root` and a symlink pointing out of the package
root is rejected; absolute entry paths are refused; permissions are checked at
dispatch; three consecutive handler failures disable an extension until
`runtime_reenable`. Out-of-process (worker/WASM) hosting is declared in the
contract but **not yet implemented** — builtins run in-process today.

## 7. Testing

Copy the walking skeleton
(`test/03_system/ide/extension_kernel_walking_skeleton_spec.spl`): prove the
extension is discovered *without* executing, then that dispatch activates it,
runs the real handler, and that deactivation disposes every registration.

Never assert that a source file contains a symbol — that passes while the code
does nothing (318 such assertions were deleted from this area). Run one spec at
a time with `SIMPLE_TIMEOUT_SECONDS=900`; only the final `Results:` line is
authoritative.

## Reference

- Kernel API and landmines: `doc/00_llm_process/layer_expert/editor_extensions/skill.md`
- Feature overview: `doc/00_llm_process/feature_expert/ide_extension_kernel/skill.md`
- VS Code bridge: `src/app/vscode_extension/manifest_{check,gen}.spl`
