# Low Dependency UI dynSMF Detail Design

Date: 2026-06-05

## Selection

Selected design: implement the dependency gates and stdlib-like dynSMF session
behavior for the six requested default libraries.

## Components

| Component | Responsibility |
|-----------|----------------|
| `UiDependencyClosure` | Exact-prefix import closure model |
| `UiDependencyPolicy` | Allow/deny rules for TUI, renderer, adapters, widgets |
| `RendererCapability` | Explicit lazy boundary for HTML/CSS-capable widgets |
| `DynSmfManifestEntry` | Stable dynSMF library metadata |
| `DynSmfBuildPlan` | Deterministic compile command for precompiled SMF outputs |
| `DynSmfArtifactStatus` | Runtime readiness result for generated `.smf` artifacts |
| `DynSmfSession` | Session-owned handle, generation, policy, evidence state |
| `DynSmfEvidenceRow` | Deterministic load/skip/symbol/stale/unload/reload evidence |
| `dynsmf_autoload` | Startup adapter from CLI/env policy to checked session autoload |

## Data Structures

```sdn
UiDependencyPolicy {
  lane: text
  allowed_prefixes: [text]
  forbidden_prefixes: [text]
  forbidden_terms: [text]
  capability_exceptions: [text]
}

DynSmfManifestEntry {
  id: text
  path: text
  source_module: text
  artifact_kind: text
  abi_version: text
  default_autoload: bool
  capability_tags: [text]
  exports: [text]
  dependencies: [text]
}

DynSmfSession {
  session_id: text
  generation: int
  next_handle: int
  disabled_all: bool
  disabled_ids: [text]
  loaded: [DynSmfLoadedLibrary]
  evidence: [DynSmfEvidenceRow]
}

DynSmfBuildPlan {
  library_id: text
  source_module: text
  source_path: text
  output_path: text
  command: text
  status: text
  reason: text
}

DynSmfArtifactStatus {
  library_id: text
  path: text
  ready: bool
  reason: text
  byte_count: int
  magic_hex: text
}
```

## Algorithms

### Exact-Prefix Import Closure

1. Build a module map from `src/app`, `src/lib`, and `src/os`.
2. Parse Simple `use` and `export use` statements.
3. Resolve imports to the longest existing module prefix.
4. Traverse from the root lane.
5. Apply lane policy to resolved modules and unresolved forbidden imports.
6. Report deterministic violation paths.

`app.ui.tui` must not match `app.ui.tui_web`.

### Renderer Capability Load

1. Widget declares capability id.
2. Generic renderer builds without implementation imports.
3. Capability registry resolves requested implementation.
4. HTML/CSS implementation loads only for capability users.
5. Non-HTML widgets emit no HTML/CSS capability request.

Current slice: `app.ui.render.widgets` is reduced to a TUI-only compatibility
wrapper. HTML tests and the production `wm_compare` caller import
`app.ui.render.html_widgets` directly. The dependency gate also checks the real
web, Tauri, Electron, browser, VSCode, TUI-web, and headless web-render adapter
sources so HTML-capable adapters cannot regress to the shared TUI widget shim.
Where an adapter renders shared web output, the gate verifies a direct
`common.ui.web_render_api` import.

`app.ui.render.capability` holds implementation-free capability metadata:
`html_renderer -> app.ui.render.html_widgets`, `css_provider ->
app.ui.render.css`, and `tui_renderer -> app.ui.render.tui_widgets`.
HTML/CSS capabilities are lazy; TUI renderer remains default-autoload.
`css_for_components([...])` deduplicates known style components and skips
unknown names, giving adapters a deterministic payload selector for only the
styles they need.

### dynSMF Session Startup

1. Parse args/env/test policy.
2. Load manifest entries.
3. Apply skip-all and per-id disable.
4. Validate enabled default precompiled SMF artifacts exist and start with
   `SMF\0`.
5. Load ready entries through `smf_dlopen_checked`.
6. Emit evidence rows.

### App Startup Integration

1. Read `SIMPLE_DYNSMF` and `SIMPLE_DYNSMF_DISABLE`.
2. Combine those values with the app-root CLI args.
3. Construct and checked-autoload a session through
   `app.startup.dynsmf_autoload`.
4. Keep plain app-root startup quiet.
5. Print summary and evidence rows only for `--dynsmf-status`.

### dynSMF Artifact Readiness

1. Convert manifest metadata and artifact bytes into `DynSmfArtifactStatus`.
2. Reject non-`precompiled_smf` entries, missing paths, missing files, short
   files, and invalid magic with deterministic reasons.
3. Accept only artifacts whose first four bytes are `83, 77, 70, 0`
   (`SMF\0` / `534d4600`).
4. In checked load paths, route through `smf_dlopen_checked` so the lower
   facade validates extension, existence, and magic before returning a handle.

### dynSMF Artifact Build Plan

1. Map each manifest id to a concrete repo source path.
2. Validate the artifact kind is `precompiled_smf` and output path ends in
   `.smf`.
3. Emit `bin/simple compile <source_path> -o <output_path>`.
4. Report invalid source/output metadata before any package wrapper executes a
   build.

### dynSMF Unload/Reload

1. Resolve library id in session.
2. Close lower dynlib handle through `smf_dlclose`.
3. Mark entry unloaded and increment generation.
4. Resolve symbols through `smf_dlsym`; append symbol evidence for successful,
   missing, and stale/unloaded lookups.
5. Reload unloaded ids with fresh handle metadata and a `reload` evidence
   action; already-loaded ids are not duplicated by repeated autoload.
6. System coverage exercises the representative export for every selected
   default id: `open`, `connect`, `draw`, `render_html`, `render_gui`, and
   `render_tui_tree`.

## Failure Handling

| Failure | Response |
|---------|----------|
| Forbidden dependency | Return violation with source, target, and path |
| Missing capability | Return missing-capability diagnostic |
| Unknown dynSMF id | Record failed evidence with `unknown_library` |
| Disabled dynSMF id | Record skipped evidence with policy source |
| Missing or invalid dynSMF artifact | Record failed evidence from `smf_dlopen_checked` |
| Load failure | Record lower loader error |
| Lookup after unload | Record stale/unloaded diagnostic |

## Implementation Order

1. Add failing dependency-gate spec.
2. Add failing dynSMF session spec.
3. Implement exact-prefix analyzer and policy fixture.
4. Implement dynSMF session/policy/evidence module.
5. Split or gate `app.ui.render.widgets -> app.ui.render.html_widgets`.
6. Add direct adapter import checks for HTML widget and shared web-render
   contract boundaries.
7. Add renderer capability registry and HTML/CSS lazy capability declarations.
8. Migrate render adapters to component-scoped CSS selection.
9. Add the dynSMF build-plan evidence wrapper.
10. Wire app startup to dynSMF autoload policy and status evidence.
11. Add checked artifact-readiness validation for startup and system evidence.
12. Generate manuals and verify.
