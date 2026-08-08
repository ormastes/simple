# Feature Expert: IDE Extension Kernel

Status: v1 landed 2026-07-29. Plan + full commit ledger:
`doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`
(Execution status section). Coordination log: `.spipe/ide_extension_kernel/state.md`.

## What it is
Typed Simple-native extension system for the IDE. Static `extension.sdn`
manifests (schema `simple.ide.extension/1`) are decoded by
`src/lib/editor/extensions/manifest_sdn.spl` (all-issues diagnostics with real
line/col, incl. duplicate keys); behavior binds through typed registrations on
`ExtensionHost` (`src/lib/editor/extensions/host.spl`).

## Key entry points
- `contract.spl` — ExtensionId, SemVer ranges, descriptors.
- `registry.spl` — CommandRegistry (fn-value handlers, first-wins, Disposable).
- `api.spl` — Disposable, ExtensionLifetime, CancellationToken, WhenPredicate.
- `settings.spl` / `menus.spl` / `keybindings.spl` — Wave-2 registries.
- `runtime.spl` — canonical path containment (real symlink resolution via
  `rt_path_absolute`), default-deny permissions, 3-strike crash containment.
- `builtin/index.spl` — 14 builtin manifest providers + activation hooks
  (extensions self-register on activation, e.g. sheets `DOUBLE`, slides
  `title_diagram`).
- Document service: `src/lib/editor/document/` (registry, transactions, undo,
  multi-view invalidation, autosave, SDN hot exit; DocumentCodec trait —
  Writer save + Sheets workbook codec implement it).
- Live capability truth: `src/app/ide/capabilities.spl`
  `ide_capabilities_live()` (declared/indexed/activatable/bound).
- VS Code bridge: `src/app/vscode_extension/manifest_{check,gen}.spl`.

## Conformance fixture
`test/fixtures/ide_extensions/hello/` + walking-skeleton system spec
`test/03_system/ide/extension_kernel_walking_skeleton_spec.spl` (discover
without execution → lazy activation → real handler → disposal).

## Docs
- Authoring guide: `doc/07_guide/app/ide/extension_authoring.md`
- Layer view: `doc/00_llm_process/layer_expert/editor_extensions/skill.md`
- Office suite reality check: `doc/07_guide/app/ide_office_plugin_suite.md`
  (§Implementation status)

## Landmines specific to this feature
- Build manifest structs via `mut` locals — `SdnValue.insert` on
  constructor-returned dicts mutates a dead copy.
- Class instances in array FIELDS lose mutations — registries use
  struct-entry + whole-array-reassignment (see `function_registry.spl`).
- SDN literals with `{}` in specs need raw `'...'` strings (interpolation).
- Dispatch is linear-scan + event-log per call — too heavy for per-keystroke
  paths (filed; keep hot paths direct until a provider handle API exists).
