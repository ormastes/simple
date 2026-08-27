# Simple Office + UI SSpec — Typed UI Interface Research (2026-08-16)

Status: SAVED, fact-check pass pending (see "Fact-check corrections" section at end;
this file is the authoritative saved copy of the external research input; the
repo-verified architecture lives in
`doc/04_architecture/ui/testing/typed_ui_interface_arch.md` and the parallel-agent
plan in `doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md`).

## 1. Core recommendation

Do not "add more UI selector syntax." Instead: **treat the UI ID graph as a
compiled, versioned application interface.**

Pipeline:

```
UI source (.spl builders / .sui templates / dynamic typed ID patterns)
  → Compiled UI Interface (ID manifest, generated SSpec symbols, compat lock, source locations)
  → One semantic UI tree (TUI, GUI/Web/DrawIR, accessibility, test/action interface)
  → Compiled SSpec ActionPlan (real TUI input, real GUI input, CLI setup, headless semantic)
  → Before/Action/After evidence
  → Generated human-readable manual (Markdown)
```

First reference implementation: **Calc** (stable cell IDs, deployed TUI flow,
GUI/web access, formulas, system-test evidence already exist).

## 2. Current-state audit (as claimed by research; see corrections at end)

Sound foundations: explicit builder IDs; UiAccessNode (canonical_id, surface_id,
widget_id, kind, focus, state, actions, children); `surface#widget` canonical
encoding; UITree find_widget/all_widget_ids; rich UIEvent vocabulary; SGTTI
shared test substrate; typed SSpec evidence (selector cardinality, oracles,
terminal regions, pixel regions, manual blocks, provenance); action trace with
before/action/after; manual renderer; Office command/feature registries.

Critical gaps:
- A. Flat widget IDs overwrite/alias (process-level `_widget_registry`,
  `upsert_widget_record` replaces same-id records; child links are ID strings;
  session WidgetStore exists but flat and little-adopted). Identity storage
  itself must become scope-safe (QML model: unique per component scope).
- B. SGTTI runtime resolution not strict — may return first match; need
  "exactly one or error" (WebDriver/Playwright strictness principle).
- C. `.sui` has no real template AST — raw template string + regex event
  extraction; compile-time ID checking impossible until fixed.
- D. Accessible-name extraction incomplete — snapshot reads `get_prop("text")`
  but widgets store label/content/title/value/placeholder/alt.
- E. Calc has two semantic UI descriptions — SheetsApp widget tree vs a
  manually built CalcAccessController tree with hand-written JSON.
- F. Office system testing relies on string containment, not the evidence
  system.
- G. Theme authority split — fluid_light default + liquid alias exist, but
  UITree GlassDark fallback, hardcoded Office iOS-style helper, per-app
  fallbacks, blur applied to content widgets.

## 3. Frozen selector and identity contract

Authored SSpec:

```
# @ui: app.office.calc
# @ui-target: both

it "calculates a formula":
    click cell_A1
    type "6"
    press Enter
    click cell_B1
    type "=A1*A2"
    press Enter
    expect cell_B1 value "48"
    show screen
```

- `# @ui:` is SSpec metadata, not new punctuation.
- Bare identifier = compiled UI ID reference (compile-time checked).
- Dotted identifier = qualified path (`toolbar.save`).
- Quoted string = accessible-name fallback (runtime strict, secondary).
- `id(expr)` = explicit runtime-ID escape hatch.
- Omitted target = focused element.

Precedence: generated symbol → qualified path → typed dynamic pattern →
explicit runtime ID → accessible-name fallback.

Duplicate rules: local ID unique within its semantic component scope; shortest
globally-unique suffix importable as convenience symbol. Ambiguous short ID =
SSpec compile error (UIE1004 listing qualified candidates + declaration sites).
Duplicate local ID within one scope = UI compile error (UIE1002, both source
locations). Unknown ID = UIE1001 with did-you-mean + manifest path +
declaration site. No first-match/traversal-order fallback, ever.

## 4. Compiled UI interface

Core types: UiLocalId, UiScopePath, UiQualifiedId, UiNodeKey{tree_instance,
surface_id, qualified_id}, UiIdPattern{prefix, value_type, codec_id},
UiInterfaceNode{qualified_id, kind, actions, public, required, dynamic_pattern,
source_file/line/col}, UiInterfaceManifest{schema_version, app_id,
interface_version, source_hash, surfaces, nodes, aliases, patterns}.

- UiNodeKey (not flat text) is store identity; WidgetNode keeps `id()` /
  `qualified_id()` / `canonical_id()` facade.
- Semantic scope, not visual ancestry: only intentional component/domain
  boundaries create scope segments (`toolbar.save`, `sheet.cell_A1`), never
  layout wrappers. Authoring: `ui_scope("toolbar", [...])`, components take a
  `UiScope` param.
- Public vs private nodes: interactive controls, domain-addressable items,
  focus/selection owners, required status outputs are public; layout panels
  and decoration private. Generated SSpec symbols expose public only.
- Compatibility lock at `build/ui-locks/<app>.ui.lock.sdn`: adding public ID
  compatible; renaming/removing public ID, removing action, incompatible kind
  change = breaking. Transitional `aliases:` with deprecated_since/remove_after.

## 5. ID extraction

- `.spl`: post-name/type-resolution extraction pass keyed on resolved builder
  symbols; builder descriptors in an SDN registry (id_argument, kind, actions).
  Literal and const-evaluated IDs → static nodes; runtime-only IDs flagged
  unless builder marked private.
- `.sui`: real template AST (Element/Text/Expression/If/For/ComponentEmbed
  with source spans); one compiler emits semantic WidgetNode build, HTML/DrawIR
  render, hydration bindings, interface nodes, accessibility names, source
  maps. No separate web-only vs TUI-only IDs.
- Dynamic IDs: typed patterns (`cell_{CellRef}` with codec), stable document
  IDs preferred over positional (`slide_7f4c2a` not `thumb_0`); positional
  aliases only for ordering tests.

## 6. Identity-store refactoring (expand → migrate → contract)

Expand: UiNodeKey + session-owned WidgetStore behind existing WidgetNode(id)
facade; duplicate validation on tree build (warning normally, error in
strict/mission-critical and always in SSpec compile).
Migrate order: WidgetNode/WidgetStore → UITree → layout → renderers → access
snapshots → SGTTI/drivers → Office apps. Preserve `surface#widget` wire
encoding; add `scope_path` additively.
Contract: remove global mutable store, silent upsert, first-match queries;
keep compat decoder for old captures; require aliases for renamed public IDs.

## 7. Unified SSpec UI ActionPlan

UiActionPlan{interface_id, target_surfaces, setup, actions, assertions,
captures}; UiActionStep{kind, target, value, preconditions, settle, source};
UiTargetRef ∈ {StaticId, QualifiedId, PatternId, Focused, ExplicitRuntimeId,
AccessibleNameFallback}.

Execution law (every live action): verify manifest/source hash → pre snapshot
→ resolve cardinality-one → verify visible/enabled/action-supported → get
semantic+geometric target → deliver real surface input → wait settle → post
snapshot → read-after-write verify → record everything.

UiTestDriver interface (snapshot/resolve/click/focus/type_text/press/drag/
scroll/wait/capture) with adapters: headless semantic, TUI in-process, TUI PTY,
GUI compositor, Web, HTTP access (remote-process semantic), SimpleOS
compositor. SGTTI = shared query substrate, not mutation owner.

`@ui-target: both` = same ActionPlan runs on TUI and GUI sessions; compare
public IDs, semantic state, action/model results, focus/selection meaning —
semantic parity, never pixel parity.

## 8. Assertion hierarchy

L0 manifest (existence/kind/action/duplicate) → L1 semantic snapshot
(value/focus/enabled/visible/model) → L2 terminal grid / DrawIR (relative
layout, hit box, style roles) → L3 pixel comparison (theme regression,
controlled env, explicit masks) → L4 deployed workflow (process boundaries,
persistence, recovery, perf). Use the cheapest reliable oracle. SSIM/LPIPS
diagnostics only, never sole oracle.

## 9. TUI testing

Small terminal-state machine (cursor, erase/insert, SGR, alt screen, scroll
regions, cursor visibility, OSC links, grapheme clusters, wide/combining/emoji
cells). Canonical TerminalCell/TerminalFrame with semantic_id per cell region.
Grapheme segmentation per UAX #29; East Asian Width with terminal tailoring.
Semantic overlay annotation from the access tree (evidence-time, not
production render). Matching modes: exact frame, semantic region, text-region
subset, attribute-aware, cursor, focus treatment, layout relation, masked
dynamic region.

## 10. GUI/web testing

ID → semantic node → DrawIR rect → hit rect → pointer anchor → move/down/up.
Evidence: canonical ID, rects, exact coordinates, trajectory, source line,
pre/action/post screenshots, semantic + DrawIR diffs (Playwright-trace-style).
Focus: semantic check in functional tests; visual focus-ring check in
theme/accessibility tests.

## 11. Manual-generating SSpec

ActionPlan is the sole source of truth; the manual is a projection (no
duplicated prose workflows). Required structure: purpose, prerequisites,
fixture/setup, human UI steps, optional CLI fast setup (shown explicitly),
expected result, before/action/after evidence, troubleshooting, artifacts,
provenance. `show screen` lowers to a capture checkpoint (TUI: semantic +
normalized frame + annotated md; GUI: semantic + DrawIR + screenshot + SVG
overlay; both: parity table). Options: `target <id>`, `region <id>`,
`compare "<baseline>"`, `theme`. Default surface: TUI; GUI required for
drag/geometry/canvas/visual; CLI preferred for fixtures only.

## 12. Liquid theme

Evolve existing fluid family into simple_liquid_light/dark with compat aliases
(fluid_light, liquid, glass names). Material hierarchy per Apple Liquid Glass
guidance: glass only for controls/navigation chrome (toolbar, sidebar,
dialogs, transient controls); content surfaces (Writer page, Calc grid, Slides
canvas, Draw canvas, tables/forms) opaque. One ThemeService
(active_theme/snapshot/resolve(role)/accessibility_preferences); shared
semantic roles (chrome, content, content_elevated, selection, focus, accent,
danger, text_primary/secondary, disabled, grid_line, page, canvas). TUI
mappings never color-only (focus = border+bold, selection = reverse/brackets,
error = color+marker, disabled = dim+state). Tests split: functional
(theme-independent), theme contract (tokens/contrast/reduced-transparency/
motion/focus), limited visual integration set.

## 13. Target Office architecture

Layers: app.office.kernel (DocumentSession, CommandBus, QueryBus, Selection,
UndoRedo, Clipboard, SearchReplace, Autosave, Recovery, RecentFiles, FileLock,
Diagnostics) / app.office.model.{writer,calc,slides,draw,base,math} /
app.office.service (Formula, Chart, Spell, Layout, Media, Print, Export,
Collaboration) / app.office.format (Package, ODF, OOXML, CSV, Markdown, HTML,
SVG, PDF) / app.office.ui (views + shared components + UI manifests) /
app.office.adapter (CLI, TUI, GUI, Web, SimpleOS) / app.office.extension.
MDSOC+: shared parent contracts, no private sibling imports, commands/service
tokens cross boundaries, declared extension points only, heavy services
dynamically loadable, standalone launch doesn't pull IDE/compiler.

One command path: every UI/TUI/CLI/automation/plugin operation → typed
OfficeCommand → DocumentSession → model mutation → semantic view update
(e.g. writer.format.bold, calc.cell.commit, slides.slide.add,
office.document.export_pdf).

Formats: ODF 1.4 (OASIS standard since 2025-10-06) as first interchange
target; OOXML adapters package-part based (OfficePackage: parts,
relationships, content types, media, metadata, lossless unknown parts). Per-app
domain models, no giant common AST. No compatibility claims until corpus
round-trip gates pass.

## 14. Feature scope (P0/P1 acceptance targets)

Shared P0: lifecycle, sessions/dirty/lock/conflict, undo/clipboard/selection/
find-replace/history, autosave/recovery/atomic save/diagnostics, UI shell,
keyboard-only + pointer + touch + IME + dnd, accessibility, print/PDF,
format registry + round-trip report, extension points, testing infra.
Writer P0: paragraphs/runs/formatting/styles/lists/tables/links/images/page
setup/headers-footers/find-replace/word count/undo/autosave/Markdown-HTML-ODT-
DOCX-stages/PDF. P1: comments, track changes, footnotes, TOC, fields, mail
merge, columns.
Calc P0: workbook/sheets, selection/nav, formula editing + dependency graph +
recalc, ref types, OpenFormula core + errors, number formats, row/col ops,
freeze/scroll/merge, sort/filter/find, validation + conditional formatting,
basic charts, CSV/ODS/XLSX-staged/PDF. P1: named ranges, pivots, external
refs, connectors, goal seek.
Slides P0: slide lifecycle, layouts/masters/themes, elements, transform ops,
align/group/z-order, notes/comments, slideshow/presenter, ODP/PPTX-staged/PDF/
image export. P1: transitions, animations, AV, custom shows.
Draw P0: pages, shapes, connectors+routing, transforms, group/layers/z,
grid/snap/guides, fill/stroke/gradients, SVG/ODG/PDF. P1: bézier, booleans.
Base/Math/Mail/Notes/Planner/Dashboard: same kernel/command/theme/ID/test
infra; never block Writer/Calc/Slides P0.

## 15. Manual-ready SSpec catalog

Shared scenarios (new→edit→save→reopen, save-as, undo/redo, clipboard,
find/replace, autosave/recovery, malformed file, keyboard-only, reduced
transparency, round trip) + per-app catalogs (see plan doc). Evidence bundle
per scenario: compile/ (ui-interface-check, source-map), trace/ (action-plan,
before/action/after), tui/ (ansi + frame.sdn + annotated.md), gui/ (pngs,
draw-ir, overlay.svg), model/ (before/after/diff), artifacts/, manual/,
receipt/ (manifest, hashes, run-id). Evidence policy sets minimum per
scenario.

## 16. Phases (0–10)

0 contract freeze + feature ledger → 1 identity safety → 2 UI interface
compiler → 3 ActionPlan + unified drivers → 4 evidence/manual projection →
5 Calc reference vertical slice → 6 shared kernel + theme authority →
7 Writer → 8 Slides/Draw → 9 formats/Base/Math/companions → 10 contract &
cleanup. Each phase expand→migrate→contract with explicit exit gates (see
plan doc for gates and the parallel-agent ownership matrix A–M).

## 17. Acceptance gates

Compile-time: unknown/duplicate/ambiguous ID, wrong action, wrong kind,
pattern validation, lock compatibility. Runtime: manifest/source-hash match,
cardinality one, capability, read-after-write, revision correlation, real
input in system tests, cleanup. Rendering: TUI frame correctness, GUI
semantic+hit+DrawIR+controlled pixels, both=semantic parity, theme gates,
fixed visual-baseline config. Office: save/reopen model preservation,
recovery, undo consistency, round-trip loss reports, no unproven compat
claims, no cross-capsule load bloat, one command contract across CLI/TUI/GUI,
no test-only code in production closure. Manual: complete deterministic
manual, stale evidence rejected.

## 18. First milestone: Calc Typed UI Contract v1

1) scoped identity storage (no silent overwrite, strict ambiguity);
2) Calc manifest (formula_input, confirm_edit, sheet_grid, cell_{CellRef},
source locations, actions); 3) generated symbols (cell_A1/A2/B1,
formula_input, confirm_edit); 4) compile-failure fixtures (misspelled/
duplicate/ambiguous/unsupported-action); 5) one Calc semantic view (delete
second access tree + hand JSON); 6) unified live flow (6, 8, =A1*A2 → 48 on
TUI and GUI, keep 20×30 grid + deployment/perf evidence); 7) generated manual
(annotated frame, screenshot+overlay, IDs, state, provenance); 8) Simple
Liquid integration (glass chrome, opaque grid, semantic tokens, TUI roles).

## Fact-check corrections (repo-verified 2026-08-16)

Verified same-day against the repo. Corrections to §2 above:

- **Theme (§2.G confirmed, with nuance)**: `config/themes/theme.sdn:1` sets
  `default_theme: fluid_light` and line 18 aliases `liquid: fluid_light`;
  `aetheric_dark` (`theme_package.spl:97`) is only the fallback when the
  registry file is missing. App-local hardcoding is real: generated
  `fluid_light_theme_snapshot.spl` consumed directly by SimpleOS WM bootstrap
  and devhub GUI; iOS-style Office helper (`src/lib/common/ui/ios/theme.spl`,
  `src/app/office/theme.spl`); GlassDark fallback in `widget.spl:114`.
- **UiAccessNode field is `focused: bool`**, not `focus`
  (`src/lib/common/ui/access_types.spl:11-16`). Encoding `surface#widget` with
  `main` default confirmed.
- **`.sui` exists only in the Rust seed** (`src/compiler_rust/parser/src/sui_parser.rs`,
  raw `template: String` + char-scan variable extraction; web compiler
  `web_compiler.rs:269` is explicitly regex-based). No pure-Simple `.sui`
  pipeline exists — the template-AST work is seed-side or a new pure-Simple
  compiler.
- **Office web adapter**: only Calc has an HTTP access host
  (`src/app/office/sheets/access_server.spl`,
  `calc_access_session_host.spl`) — JSON snapshot polling, no websocket, no
  hydration. Writer/Slides/others have offline `html_render.spl` only.
- All other §2 claims CONFIRMED with evidence: flat `_widget_registry`
  (`src/lib/common/ui/widget_store_ops.spl:20,54-78,204-206`), marginal session
  `WidgetStore` (`widget_store.spl`, used in `nogc_sync_mut/ui/session.spl`),
  `find_widget`/`all_widget_ids` + GlassDark fallback
  (`src/lib/common/ui/widget.spl:192,196,114`), SGTTI first-match
  (`src/lib/nogc_sync_mut/ui_test/sgtti.spl:252-255`), snapshot
  `get_prop("text")` gap (`access_snapshot.spl:206`), Calc dual tree + hand
  JSON (`sheets_app.spl:48`, `access_controller.spl:129-134,190,221,231,282`),
  evidence model (`src/lib/common/spec/evidence/`), Writer undo/commands/app-store
  workaround (`word_app.spl:8-15,27,177-178`), Slides index-derived element IDs
  (`slides_app.spl:155`).
- **Existing web/remote assets the research missed** (used by the new Web Host
  lane): `src/app/ui.web/` full stack incl. `host_adapter_contract.spl`,
  ws handlers, session tokens, origin guard; `src/app/ui.vscode/`
  (`backend.spl`, `protocol.spl`) VSCode-protocol UI backend;
  `src/app/ui.tui_web/` screen-to-HTML; enterprise `http_core`
  (`src/lib/common/net/http_core.spl`) with hardened limits/smuggling/path
  safety — the mandated HTTP substrate for any new hosted UI.
