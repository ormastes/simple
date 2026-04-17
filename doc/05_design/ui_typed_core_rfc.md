# UI Typed Core RFC

**Status:** Phase 0 (active)
**Created:** 2026-04-17
**Owner:** UI library modernization
**Master plan:** `doc/01_research/ui_modernization_plan.md`

## 1. Context

The Simple UI library (`src/lib/common/ui/`, ~50 files) is broad but its core model is heavily string-driven: `WidgetRecord.kind` and `WidgetRecord.layout` are `text` (widget.spl:48-51), ~20 `with_*` modifiers are proto-fluent free functions (builder.spl:340-459), theme variants and action dispatch use raw strings, and iOS/Glass platform builders pollute the public surface.

What already works: `enum SizeClass`/`Orientation` (profile.spl:17-22), `enum UIMode`/`UIEvent`/`PatchKind`/`Capability`, and the mature `UISession` architecture (session.spl:28) which separates description (`UIState`/`WidgetStore`) from runtime (`Viewport`/`ChangeLog`/`SurfaceManager`/`ProfileResolver`).

This RFC is the canonical contract for the 10-phase migration. It captures Phase 0 investigation answers, the codec strategy, per-phase exit gates, and known compiler-level blockers that affect downstream phases.

### 1.1 Goals

1. Eliminate stringly-typed semantic fields from the *internal* UI model
2. Deliver fluent dot-chain authoring on `WidgetNode`
3. Preserve the wire contract byte-identical (web/TUI/CLI/IPC v1)
4. Extract platform builders (iOS/Glass) from the core public surface
5. Update UI skill, syntax docs, and architecture docs

### 1.2 Non-goals (this RFC)

- Replacing the ~50 hex/rgba color string literals with typed `Color`/`Rgba` (tracked as Phase 11 follow-up)
- Replacing the JSON wire format with SDN (orthogonal; would break IPC v1 clients)
- Migrating SimpleOS or browser app code beyond what's needed for downstream-build verification

## 2. MDSOC+ alignment

Per `feedback_mdsoc_plus_default.md` (2026-04-17), MDSOC outer + ECS business layer is the default for SimpleOS userland and apps. UI is userland. This RFC models:

- `WidgetNode` / `WidgetRecord` as **MDSOC components** — immutable description nodes; no behavior baked in
- `UISession` / `UIState` / `WidgetStore` as the **ECS world** — entities = node IDs, components = props/style/lifecycle, systems = layout/render/event-dispatch
- `UIEventBus` and lifecycle dispatch as **ECS systems** that operate on the world per frame

Typed enums (Phase 2) are component schemas. Fluent `WidgetNode` methods (Phase 3) are component-builder ergonomics, not behavior — they keep the description immutable and ECS-friendly.

## 3. Phase 0 investigation results

### 3.1 Test assertions on raw strings — narrow scope

Audited:
- `test/unit/app/ui/gui_widgets_spec.spl` — placeholder tests only; no raw kind/layout/variant assertions
- `test/unit/app/ui/backend_matrix_spec.spl` — exactly **one** raw assertion at line 36: `expect(main.layout).to_equal("hbox")`

Decision: Phase 2 updates the single assertion at `backend_matrix_spec.spl:36` to compare against `LayoutKind.Hbox` directly (or asserts via `.layout.to_wire() == "hbox"`). No broader test-helper rewrite is required.

### 3.2 SMF manifest files — out of scope

`src/lib/common/ui/builder.smf` and `access_store.smf` are **binary compiled artifacts** (~219 bytes each), not text manifests. They do not encode kind strings. Phase 2 does not touch them; they regenerate from updated `.spl` sources during build.

However, `builder.spl` itself contains 22+ widget kind string literals at constructor sites (lines 25, 62, 75, 81, 88, 95, …) that flip to `WidgetKind.X` enum constructors in Phase 2. Also `widget.spl:67-115`'s `parse_widget_kind` function returns `text` and contains 38 kind name mappings (including iOS-specific `navigation_bar`, `tab_bar`, `card`, `switch`, `segmented_control`, `search_bar` and Glass-specific `glass_title_bar`, `sidebar`, `command_bar`, `workspace_tabs`, `command_palette`, `toast`, `sheet_modal`, `context_menu`, `inspector`, `utility_rail`, `status_chip`, `selection_pill`, `empty_state`).

### 3.3 Core→platform import cycles — confirmed (4 files)

| File | Line(s) | Imports | Used as |
|------|---------|---------|---------|
| `src/lib/common/ui/style.spl` | 150, 153, 156, 159 | `common.ui.ios_theme.{ios_light,ios_dark}`, `common.ui.glass_theme.{glass_light,glass_dark}` | factory call → returns `UITheme` |
| `src/lib/common/ui/simple_theme.spl` | 5 | `common.ui.glass_tokens.{GlassDesignTokens, StitchMetadata, GlassColorTokens, StitchMd3Colors}` | class field types |
| `src/lib/common/ui/theme_sync_sdn.spl` | 19 | `common.ui.glass_tokens.{StitchDesignSystem, StitchMetadata, StitchMd3Colors}` | serialization types |
| `src/lib/common/ui/icon_registry.spl` | 6 | `common.ui.glass_numeric_tokens.{GLASS_ICON_TERM, GLASS_ICON_FILES, ...}` | RLE icon constants |

Decision: Phase 1 introduces `ThemeRegistry` (`src/lib/common/ui/theme_registry.spl`) that exposes:
- `ThemeRegistry.get(theme_id: ThemeId) -> UITheme`
- `ThemeRegistry.tokens(theme_id: ThemeId) -> DesignTokens`
- `ThemeRegistry.icons(theme_id: ThemeId) -> IconSet`

Platform modules register at module-init time. Core consumers call the registry; no direct platform import remains in core.

## 4. Compiler-level constraints (newly discovered)

### 4.1 Chained methods are broken (`.claude/rules/language.md`)

> "Chained methods broken — use intermediate `var`"

This affects Phase 3 directly. The plan's target syntax `node.width(120).height(40).accent(Primary)` does not work in current Simple. Options:

**Option A** — Fix the chained-method bug in the compiler as a hard prerequisite to Phase 3. Scope: parser + typechecker investigation. Estimated effort: medium. Benefit: unblocks fluent style across the whole language, not just UI.

**Option B** — Phase 3 ships intermediate-`var` form first:
```
var btn = Button("save", "Save")
btn = btn.width(120)
btn = btn.height(40)
btn = btn.accent(Accent.Primary)
```
This is functionally typed but loses authoring ergonomics. Defer chain syntax until Option A lands.

**Decision:** Pursue **Option A** (fix the chain bug) as a *separate, parallel* compiler-track item. Phase 3 ships the methods regardless; users can chain immediately once the compiler fix lands without any library change. Chain syntax in examples and docs is conditional on the chain-fix landing first.

This adds a new entry to the Compiler RFC Track (Phase 9) alongside UFCS and bare-enum literals.

### 4.2 No UFCS, no bare-enum inference

Confirmed in earlier exploration. Independently tracked under Phase 9.

### 4.3 No inheritance

Per `language.md`. The iOS/Glass extraction (Phases 1, 7) cannot use class inheritance — must use composition, traits, or mixins. Already the planned approach.

## 5. Codec strategy

Wire compatibility is non-negotiable. The boundary is at the JSON encoder in `access.spl`'s `ui_access_snapshot_to_json` (called by `snapshot_wire.encode_snapshot` at snapshot_wire.spl:28).

Per-enum codec convention:

```
enum WidgetKind:
    Panel
    Button
    # ... 18 more

    fn to_wire(self) -> text:
        match self:
            Panel => "panel"
            Button => "button"
            # ...

    fn from_wire(s: text) -> Result<WidgetKind, text>:
        match s.to_lower():
            "panel" => Ok(Panel)
            "button" => Ok(Button)
            # ...
            _ => Err("unknown widget kind: {s}")
```

Each new enum (`WidgetKind`, `LayoutKind`, `ThemeId`, `StatusVariant`, `Accent`, `BorderStyleKind`, `FontWeight`) carries its codec methods. `snapshot_wire.spl` and `patch_wire.spl` are thin orchestrators. No central codec map.

Wire strings are *frozen* — exactly the strings emitted today. Adding a new enum case requires adding a wire string (forward-compatible). Removing a case is a wire-breaking change; gated by a separate RFC.

## 6. Per-phase exit gates

| Phase | Gate |
|-------|------|
| 0 | RFC + golden fixture committed; investigations resolved (this section) |
| 1 | `bin/simple build`; `backend_matrix_spec.spl`, `ipc_protocol_spec.spl`, `theme_sync_*` tests, golden fixture all pass |
| 2 | Golden-byte fixture diff = 0 bytes; `backend_matrix_spec.spl` (with line-36 update) and `ipc_protocol_spec.spl` pass |
| 3 | Phase 2 gates + new `examples/ui/fluent/` builds and runs; chain-syntax examples gated on chain-fix RFC |
| 4 | Phase 2 gates + new `token_resolution_spec.spl` |
| 5 | Phase 2 gates + new `typed_action_spec.spl`; `ipc_protocol_spec.spl` byte-identical |
| 6 | New `responsive_widget_spec.spl` covers each branch on each backend |
| 7 | **COMPLETE (2026-04-17)** — 6 platform files moved to `common.ui.ios.*` / `common.ui.glass.*` subdirs; 29 consumer files updated; 6 `pub use` shims left at old paths for one release; `examples/` and SimpleOS were already clean (no old-path references found) |
| 8 | `bin/simple build lint` flags violations with no false positives on stdlib + `examples/` |
| 9 | UFCS RFC, bare-enum-literal RFC, and chained-methods-fix RFC published under `doc/05_design/` |
| 10 | UI skill, stitch skill, theme_sync skill, syntax docs, shared_ui_contract, mdsoc+ doc all updated and cross-linked |

## 7. Risks and mitigations

| # | Risk | Mitigation |
|---|------|-----------|
| 1 | Wire bytes drift in Phase 2 | Phase 0 golden-byte fixture is the contract; CI diff per commit |
| 2 | Theme dep cycle blocks extraction | Phase 1 ThemeRegistry inversion before any module rename |
| 3 | Chain syntax not usable until compiler fix | Phase 3 ships methods; chain-form examples conditional on Phase 9 chain-fix RFC |
| 4 | `enum Action` locks out app-defined actions | `Action::Custom(text)` + `IntoAction` trait keeps it open |
| 5 | iOS/Glass kinds in `parse_widget_kind` couple core to platforms | Phase 1 splits the parser per-platform: core parses neutral kinds; platforms register their own kinds with `ThemeRegistry.register_kind(...)` |
| 6 | New enum case added without wire string → silent breakage | Lint in Phase 8 enforces every enum case has a `to_wire`/`from_wire` arm |
| 7 | Two API styles (`with_*` and method) confuse users | Mark `with_*` legacy in Phase 3 docs; lint after Phase 8; remove after UFCS lands |

## 8. Execution discipline

- Per `feedback_parallel_sonnet.md` and `feedback_parallel_scope_partition.md`: Phases 2, 4, 6 split into parallel Sonnet agents with disjoint file scope (one agent per enum, no overlap)
- Per `feedback_force_push_kernel_arc.md`: ≤5-file atomic commits with `git log` verification after each push
- Per `feedback_destructive_upstream_detection.md`: file-count guard before+after each `jj rebase`
- Per `feedback_no_branches.md`: all work on `main`, no branches
- Per `feedback_write_tool_silent_drops.md`: after each Write/Edit on touched files, verify with `wc -l + md5sum + grep`
- Per `feedback_mcp_cache_off_by_default.md`: keep MCP wrappers on `.spl`; do not enable `SIMPLE_MCP_USE_CACHE`

## 9. References

- `doc/01_research/ui_modernization_plan.md` — master plan with all 10 phases
- `src/lib/common/ui/widget.spl:48-51` — current `WidgetRecord` definition
- `src/lib/common/ui/snapshot_wire.spl:28` — wire encoder entry point
- `src/lib/common/ui/access.spl` — `ui_access_snapshot_to_json` (the actual JSON builder)
- `src/lib/common/ui/event.spl:21` — `UIEvent.Action(name: text)` wire shape
- `test/unit/app/ui/backend_matrix_spec.spl:36` — single raw layout string assertion
- `.claude/rules/language.md` — chained-methods-broken constraint
