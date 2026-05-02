# UI Library Modernization — Typed Core, Fluent API, Compiler RFC Track

## Context

The Simple UI library (`src/lib/common/ui/`, ~50 files) is broad but its core model is heavily string-driven. `WidgetRecord.kind` and `.layout` are `text` (widget.spl:48-51). ~20 `with_*` modifiers (builder.spl:340-459) take node first / return node — proto-fluent but not chainable. ~40 widget constructors. Theme variants are strings (`"primary"`, `"success"`, `"ios_light"`, …). Action dispatch is string-keyed. iOS/Glass platform builders pollute the public surface.

What already works: `enum SizeClass`/`Orientation` (profile.spl:17-22), `enum UIMode`/`UIEvent`/`PatchKind`/`Capability`, and the `UISession` architecture (session.spl:28) which already separates description (`UIState`/`WidgetStore`) from runtime (`Viewport`/`ChangeLog`/`SurfaceManager`/`ProfileResolver`).

Why now: the API is fragile (no IDE refactor, easy to misuse, easy for LLMs to generate wrong widgets), and the project's two flagship userland apps — SimpleOS (`project_simpleos.md`) and the Chromium-class browser (`project_browser_platform.md`) — both consume this surface. Modernization unblocks safe expansion.

The ask: convert the *internal* model to typed enums, deliver fluent dot-chain authoring via real methods on `WidgetNode` (no compiler change required), keep wire bytes byte-identical so the shared web/TUI/CLI/IPC contract (`backend_matrix_spec.spl`, `ipc_protocol_spec.spl`, `UiAccessSnapshot` over socket) does not break, and update the UI skill + syntax/architecture docs. Two compiler RFCs (UFCS desugar and context-inferred enum literals) ride a parallel track and unlock the final 20% of ergonomics later.

### MDSOC+ alignment

Per `feedback_mdsoc_plus_default.md` (recorded 2026-04-17), MDSOC outer + ECS business layer is the default for SimpleOS userland and apps. The UI library is userland. This plan models:

- `WidgetNode` / `WidgetRecord` as **MDSOC components** (immutable description nodes; no behavior baked in)
- `UISession` / `UIState` / `WidgetStore` as the **ECS world** (entities = node IDs, components = props/style/lifecycle, systems = layout/render/event-dispatch)
- `UIEventBus` and lifecycle dispatch as **ECS systems** that operate on the world per frame

Typed enums (Phase 2) are component schemas. The fluent `WidgetNode` methods (Phase 3) are component-builder ergonomics, not behavior — they keep the description immutable and ECS-friendly.

## Recommended approach

A 10-phase migration. Each phase is independently shippable, has explicit exit gates, and preserves the wire contract.

### Phase 0 — RFC, golden-byte fixture, and investigation **(blocker)**

Deliverables:
- `doc/05_design/ui_typed_core_rfc.md` — single canonical RFC for the migration
- Golden-byte snapshot fixture under `test/unit/app/ui/wire_golden/` capturing today's `UiAccessSnapshot` JSON for a representative widget tree (panel + row + button + dialog + toast + tabs); used as regression oracle by Phases 2–6

Investigation items (must resolve before Phase 1 starts):
- Audit `test/unit/app/ui/gui_widgets_spec.spl` and `backend_matrix_spec.spl` for raw string `kind`/`layout`/variant assertions that go *beyond* the wire boundary. **If they do, Phase 2 scope expands** to include co-located `to_wire()` use in test helpers.
- Confirm whether `builder.smf` and `access_store.smf` (sibling spec/manifest files) encode kind strings that also need updating.
- Confirm circular import: `style.spl:150-159` imports `ios_theme` and `glass_theme`; `simple_theme.spl:5` and `theme_sync_sdn.spl:19` import `glass_tokens`.

Exit gate: RFC merged, golden fixture committed, all three investigations have written answers in the RFC.

### Phase 1 — Soft iOS/Glass extraction + theme dep inversion

Move `ios_*` and `glass_*` files into `src/lib/common/ui/platforms/{ios,glass}/` subdirectories. **Public module path unchanged** — this is filesystem and import-rewiring only.

Break the cycle: introduce `ThemeRegistry` in core (`src/lib/common/ui/theme_registry.spl`). Platforms register themes at module-init time. `style.spl`, `simple_theme.spl`, and `theme_sync_sdn.spl` consume themes via the registry, not direct platform imports.

Files to change:
- `src/lib/common/ui/style.spl:150-159` — replace `import ios_theme/glass_theme` with `ThemeRegistry.get(ThemeId.IOSLight)` etc.
- `src/lib/common/ui/simple_theme.spl:5` — same pattern
- `src/lib/common/ui/theme_sync_sdn.spl:19` — same pattern
- `src/lib/common/ui/__init__.spl` — re-exports unchanged (public API stable)

Exit gate: `bin/simple build`, `backend_matrix_spec.spl`, `ipc_protocol_spec.spl`, `theme_sync_*` tests, and the Phase 0 golden fixture all pass.

### Phase 2 — Typed internal model + co-located codecs **(parallelizable)**

Add enums:
- `WidgetKind { Panel, Button, Text, Input, Checkbox, Dropdown, Image, Dialog, Statusbar, Tabs, Toast, List, Table, Tree, Menubar, Tooltip, Progress, Textarea, Label }` — derived from the 23 string values today
- `LayoutKind { Vbox, Hbox, Grid }` — from the 3 string values
- `enum ThemeId { IOSLight, IOSDark, GlassLight, GlassDark, GlassObsidianDark, ... }`
- `enum StatusVariant { Success, Warning, Error, Info }` (used by toast, status_chip)
- `enum Accent { Primary, Secondary, Success, Warning, Danger, Muted }`
- `enum BorderStyleKind { Solid, None }`
- `enum FontWeight { Normal, Medium, Semibold, Bold }`

Each enum exposes `to_wire() -> text` and `from_wire(s: text) -> Result<Self, text>` **as methods on the enum itself** (not centralized in `snapshot_wire.spl`). `snapshot_wire.spl` becomes a thin orchestrator that calls `kind.to_wire()`.

Mutate `WidgetRecord.kind: text` → `WidgetRecord.kind: WidgetKind` and `.layout: text` → `.layout: LayoutKind` (widget.spl:48-51). Update all 40 builder constructors to construct typed kinds.

Wire bytes must remain byte-identical (the golden fixture from Phase 0 is the contract).

Parallelization (per `feedback_parallel_sonnet.md` and `feedback_parallel_scope_partition.md`): split into parallel Sonnet agents, one per enum, with **disjoint file scope** — `WidgetKind` agent owns `widget.spl` + `builder.spl` builder bodies + `snapshot_wire.spl` kind codec; `LayoutKind` agent owns layout helpers; theme/variant agents own their respective theme files. No two agents touch the same file.

Exit gate: golden-byte fixture diff is **zero bytes**. `backend_matrix_spec.spl` and `ipc_protocol_spec.spl` pass unchanged.

### Phase 3 — Real `WidgetNode` methods (fluent dot-chain, no compiler change)

Add real methods on the `WidgetNode` class wrapping the existing `with_*` helpers:

```
node.width(120).height(40).accent(Accent.Primary).child(...)
```

Both forms work — `with_width(node, 120)` becomes a thin wrapper around `node.width(120)`. Update public examples and tests to chain form via codemod. Free-function form marked "legacy" in docs but not yet warned.

Headline asks reframed: this phase delivers ~80% of the user's "first param as callee object" recommendation today, *via library code only*. The remaining 20% (UFCS for arbitrary first-arg-receiver functions) ships under the **Compiler RFC Track** (see end of plan) and is not blocked by this work.

Files: `src/lib/common/ui/builder.spl`, `src/lib/common/ui/widget.spl` (add methods to `WidgetNode` class). New examples under `examples/ui/fluent/`.

Exit gate: same as Phase 2, plus new chain-form examples build and run.

### Phase 4 — Design token enums **(parallelizable per token family)**

Add `enum Spacing { Xs, Sm, Md, Lg, Xl }`, `enum Radius { None, Sm, Md, Lg, Pill }`, `enum Elevation { Flat, Low, Mid, High }`, `enum SurfaceRole { Background, Surface, Card, Overlay }`, `enum TextRole { Primary, Secondary, Muted, Danger }`.

Token resolver lives in `ThemeRegistry` (Phase 1) — maps `(ThemeId, Spacing.Md)` → pixel value, `(ThemeId, SurfaceRole.Card)` → hex color, etc.

Modifiers accept either typed token or raw value: `node.padding(Spacing.Md)` and `node.padding(16)` both compile.

Files: `src/lib/common/ui/design_tokens.spl`, `src/lib/common/ui/builder.spl`, `src/lib/common/ui/theme_registry.spl`, all theme files under `platforms/{ios,glass}/`.

Out of scope (track as Phase 11 follow-up): typed `Color`/`Rgba` to replace ~50 hex/rgba string literals.

Exit gate: golden fixture, `backend_matrix_spec.spl`, plus a new `token_resolution_spec.spl`.

### Phase 5 — Typed actions/events

Add at the public API:
```
enum CommonAction { Save, Cancel, Confirm, Dismiss, Back, Search, ToggleSidebar }
enum Action { Builtin(CommonAction), Custom(text) }
trait IntoAction { fn into_action(self) -> Action }
```

Per-app action enums implement `IntoAction`. Wire shape preserved: `UIEvent.Action(name: text)` at event.spl:30 stays a single text field; the wire `name` is `action.into_wire_name()`. Old string `with_on_action(node, "save")` remains as a deprecated overload; new code uses `node.on_action(CommonAction.Save)` or `node.on_action(MyAppAction.OpenFile)`.

Rationale for `Custom(text)` escape: the library cannot enumerate every app's actions; this keeps `Action` open by construction without breaking IPC v1.

Files: `src/lib/common/ui/event.spl`, `src/lib/common/ui/builder.spl`, new `src/lib/common/ui/action.spl`.

Exit gate: `ipc_protocol_spec.spl` byte-identical, plus a new `typed_action_spec.spl`.

### Phase 6 — Responsive widget API **(parallelizable per modifier)**

Add modifiers reusing existing `SizeClass`/`Orientation`/`ProfileResolver`:
- `node.responsive(compact = ..., regular = ..., expanded = ...)`
- `node.show_when(size_at_most = SizeClass.Compact)` / `size_at_least = ...`
- `Grid("cards").columns(compact = 1, regular = 2, expanded = 4)`

Pure additive. Files: `src/lib/common/ui/builder.spl`, `src/lib/common/ui/profile.spl`, `src/lib/common/ui/widget.spl`.

Exit gate: new `responsive_widget_spec.spl` covers each branch on each backend.

### Phase 7 — Hard iOS/Glass extraction (public module rename)

Rename module paths: `std.ui.ios` and `std.ui.glass` become the public homes for platform builders. `__init__.spl` no longer re-exports them. Old paths emit deprecation warnings but still resolve for one release.

This is the only public-API-breaking phase. Defer to last so the typed surface is stable before churn.

Exit gate: SimpleOS (`project_simpleos.md`) and the browser (`project_browser_platform.md`) both build against new paths.

### Phase 8 — Lints to deprecate stringly authoring

Add lint rules under `src/lib/lint/ui/`:
- Flag raw `kind: "button"` literal in widget construction (when public)
- Flag raw variant strings where an enum exists
- Flag raw action strings where `IntoAction` is available

Escape hatch unchanged: `node.raw_prop("css-class", "...")` stays for backend experiments, marked unstable.

Exit gate: lints surface in `bin/simple build lint` with no false positives on the standard library or `examples/`.

### Phase 9 — Compiler RFC Track (parallel, independent of Phases 1–8)

Two compiler RFCs that **generalize** the ergonomics beyond UI:
- **RFC: UFCS** — first-param-as-receiver desugar so `with_width(node, 120)` becomes call-equivalent to `node.width(120)` for *any* free function, not only library-method-mirrored ones. Lets us delete the `with_*` wrappers post-deprecation.
- **RFC: Context-inferred enum literals** — bare `Success` resolves to `StatusVariant.Success` when the expected type is known; ambiguity diagnostic if multiple enums match; `as` keyword as escape hatch. Mirrors Slint's behavior.

These are **NOT blocking** for Phases 1–8. They unlock the final cleanup (delete `with_*` wrappers; allow `Toast("saved", "Saved", Success)` without qualifier) and benefit the whole language, not just UI.

### Phase 10 — Docs and skill update

Files (with one-line intent each):

- `.claude/skills/ui.md` — current Stitch-only mockup skill; **add** sections "Typed Widget Authoring" and "Fluent Chain Patterns" with before/after snippets, point to RFC for migration map
- `.claude/skills/stitch.md` — design system reference; update token vocabulary section to mention enum tokens (Spacing/Radius/...) when generating .spl
- `.claude/skills/theme_sync.md` — sync workflow; update token-generation step to emit enum token references, not raw strings
- `doc/07_guide/quick_reference/syntax_quick_reference.md` — add **"Method Chaining / Fluent API"** section and **"Enum Construction & Inference"** section (the latter conditional on Phase 9 RFC landing)
- `doc/07_guide/language/syntax.md` — expand with fluent chain examples and (Phase 9) bare-enum literal rules
- `doc/04_architecture/shared_ui_contract.md` — add a "Wire vs Internal Types" subsection clarifying the codec boundary at `to_wire()/from_wire()`
- `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+ section) — add UI worked example showing `WidgetNode`-as-component, `UISession`-as-world, lifecycle-as-system mapping
- `doc/05_design/ui_typed_core_rfc.md` — the canonical RFC (created in Phase 0)

## Critical files (master list)

Reused (do not rewrite):
- `src/lib/common/ui/widget.spl` — `WidgetRecord`, `WidgetNode`, `UIMode`, `UIEvent` already defined
- `src/lib/common/ui/session.spl:28` — `UISession` already separates description from runtime
- `src/lib/common/ui/profile.spl:17-22` — `SizeClass`, `Orientation`, `ProfileResolver`, `LayoutProfile` already typed
- `src/lib/common/ui/snapshot_wire.spl` — orchestrator stays; codecs co-locate to enums
- `src/lib/common/ui/patch_wire.spl` — same pattern
- `src/lib/common/ui/event.spl` — `UIEvent.Action(name: text)` wire shape preserved verbatim
- `src/lib/common/ui/lifecycle.spl`, `effect.spl`, `patch.spl`, `capability.spl` — already enum-typed, no changes

Modified per phase: see each phase above.

New:
- `src/lib/common/ui/theme_registry.spl` (Phase 1)
- `src/lib/common/ui/action.spl` (Phase 5)
- `src/lib/common/ui/platforms/{ios,glass}/` (Phase 1 soft, Phase 7 hard)
- `src/lib/lint/ui/` rules (Phase 8)
- `test/unit/app/ui/wire_golden/` golden snapshots (Phase 0)

## Verification

End-to-end testing per phase:

1. **Wire stability** — `bin/simple test test/unit/app/ui/wire_golden/` — golden-byte diff must be zero through Phases 1–8
2. **Backend matrix** — `bin/simple test test/unit/app/ui/backend_matrix_spec.spl` — web and TUI must render identical snapshots
3. **IPC protocol** — `bin/simple test test/unit/app/ui/ipc_protocol_spec.spl` — protocol v1 unchanged
4. **Build** — `bin/simple build` and `bin/simple build check`
5. **Linting** — `bin/simple build lint` (Phase 8 onwards)
6. **Downstream consumers** — `examples/browser/` and SimpleOS userland build against new API after Phase 7
7. **MCP smoke** — `mcp__simple-mcp__simple_check` on changed modules; `mcp__simple-lsp-mcp__lsp_diagnostics` on `widget.spl` and `builder.spl` after each enum addition

Acceptance for the migration as a whole: all seven checks green, golden fixture diff zero, and `examples/ui/fluent/` showcases chain-form authoring end to end.

## Execution notes

- Per `feedback_parallel_sonnet.md` and `feedback_parallel_scope_partition.md`: Phases 2, 4, and 6 are inherently parallelizable per-enum or per-modifier-family. Split into parallel Sonnet agents with disjoint file scope (one agent owns one file or non-overlapping sections of one file). Phases 0, 1, 3, 5, 7, 8, 9, 10 are sequential or have small parallelizable subtasks.
- Per `feedback_force_push_kernel_arc.md`: each phase commits in ≤5-file atomic chunks, with `git log` verification after each push, so concurrent work elsewhere can't strip a wave.
- Per `feedback_destructive_upstream_detection.md`: file-count guard before+after each `jj rebase`.
- Per `feedback_no_branches.md`: all work on `main`, no branches, no orphan commits.
- Per `feedback_write_tool_silent_drops.md`: after each Write/Edit on touched files, verify with `bash wc -l + md5sum + grep`, not Read.
