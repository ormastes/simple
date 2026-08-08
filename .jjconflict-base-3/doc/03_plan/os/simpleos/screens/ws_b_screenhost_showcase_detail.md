# WS-B Detail Plan — `ScreenHost` Interface + Shared Showcase (4 Targets)

Date: 2026-08-06. Lane: `.spipe/simpleos-screens-render-lane/` (AC-3, AC-4, AC-5, AC-10).
Umbrella: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (Workstream B).
Design: `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.2, §2.3.

Goal: ONE host interface (`ScreenHost`) so the widget/showcase logic is byte-identical
across 2d / web / gui / wm and ONLY the host impl differs. Shared showcase exercises
click/drag/keytype probing, a scroll panel with scrollbar, two LINKED panels, windows,
and a toolbar widget.

---

## 0. Verified ground truth (measured 2026-08-06 — corrections to the design doc)

These were re-verified against the tree. Where they contradict the design doc or the
lane state, **this plan is authoritative** and the correction is called out.

### 0.1 `RenderBackend` importers: **8, not 7**

`src/lib/common/ui/backend.spl:23-45` declares `trait RenderBackend` with 12 methods
(`init`/`shutdown`/`render(UIState)`/`render_html(UIState)->text`/`poll_event(i32)->UIEvent?`/
4 `supports_*`/`viewport_width`/`viewport_height`/`backend_name`). **Zero `impl RenderBackend for`
exists anywhere in the tree.** `grep -c '^use common\.ui\.backend' src/**/*.spl` = **8**:

| # | File:line | Owner tree | Migration verdict (B1) |
|---|-----------|-----------|------------------------|
| 1 | `src/app/ui.electron/backend.spl:6` | `src/app/ui.*` | keep `RenderBackend` import; no change |
| 2 | `src/app/ui.none/backend.spl:6` | `src/app/ui.*` | keep; no change |
| 3 | `src/app/ui.tauri/backend.spl:7` | `src/app/ui.*` | keep; no change |
| 4 | `src/app/ui.vscode/backend.spl:7` | `src/app/ui.*` | keep; no change |
| 5 | `src/app/ui.web/backend.spl:6` | `src/app/ui.*` | keep; B5's host impl is a **new sibling file**, does not edit this one |
| 6 | `src/app/ui.tui/backend.spl:6` | `src/app/ui.*` | keep; TUI cell-grid is an explicit scope exclusion (lane state "Scope Exclusions") |
| 7 | `src/os/compositor/fb_backend.spl:15` | **`src/os/**`** | **untouched by WS-B.** Owned by WS-A/WS-C. Note only. |
| 8 | `src/os/compositor/browser_backend.spl:16` | **`src/os/**`** | **untouched by WS-B.** Owned by WS-A/WS-C. Note only. |

Design doc §1 says "imported by 7 targets" — that count is wrong (it omits one of the
two `src/os/compositor/` importers). Fix the design doc line as part of B1.

**Consequence for B1:** `ScreenHost` is **additive, not a rename**. `RenderBackend` stays
declared and stays imported by all 8. Renaming it would drag two `src/os/compositor/`
files into WS-B, colliding with WS-A/WS-C. See §1.3.

### 0.2 `common.ui.backend_factory` does not exist

Seven specs import it:
`test/01_unit/app/ui/unified_app_spec.spl:5`, `test/01_unit/app/ui/async_default_api_spec.spl`,
`test/03_system/gui/{container_detect,capability_negotiation,unified_app}_spec.spl:{35,30,34}`,
plus legacy duplicates under `test/unit/`, `test/system/`.

`ls src/lib/common/ui/ | grep factory` → empty. `grep -rn 'fn create_backend' src/` finds
only `src/compiler/70.backend/backend.spl:34` (unrelated compiler backend) and
`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl:230` (a nested fn).

**An unresolved `use` is only a WARN in this repo** — these specs are fail-open and prove
nothing about any backend. Do NOT cite them as coverage. File as a bug in B0; do not fix
inside WS-B (out of scope), but the arch check in B7 must not treat them as evidence.

### 0.3 `ShowcaseSurface` cannot express the four targets

`src/lib/common/ui/showcase_catalog.spl:5-8`:
```
enum ShowcaseSurface:
    Standalone
    HostWm
    SimpleOsWm
```
3 entries × 3 surfaces = 9 readiness bits, **all false** (`standalone_ready`/`host_wm_ready`/
`simpleos_wm_ready` at lines 36-38, 46-48, 56-58). There is **no `Web` and no `Raw2d` surface**.

Requirement "flip readiness bits per target" is unimplementable as written. **B8 owns the
schema change** (§8.2): add `Web` and `Raw2d` variants + `web_ready`/`raw2d_ready` fields,
and extend `showcase_surface_supported` (line 68) match arms. No other task edits this file.

### 0.4 `WmFsAppEvent` has no key/char and no wheel field — AC-5 keytype-on-WM is BLOCKED

`src/lib/common/ui/wm_app_process_contract.spl:17-23`:
```
struct WmFsAppEvent:
    seq: i64
    kind: text
    x: i32
    y: i32
    button: i64
    pressed: bool
```
A typed character cannot cross the WM file bridge today. AC-5 ("click, drag AND keytype
observed on every target") therefore **cannot pass on WM** without extending this struct.

**B1 owns the extension** (it is the ingress-type task): add `key_code: i64 = 0`,
`ch: text = ""`, `mods: i64 = 0`, `wheel: i32 = 0`. Backward-compatible defaults so
`src/app/wm_showcase/*` and `src/os/**` readers keep compiling. B6 consumes; B6 does not
edit the struct.

### 0.5 `DrawIrV3Scene` production path — two paths exist; showcase_core uses the value path

- **Value path (B2/B3/B4/B6 use this):**
  `widget_tree_to_draw_ir_cpu(root, w, h) -> DrawIrComposition`
  (`src/lib/common/ui/widget_draw_ir.spl:432`) →
  `draw_ir_v2_to_v3(composition: DrawIrComposition) -> DrawIrV3Scene`
  (`src/lib/common/ui/draw_ir_v2_to_v3.spl:518` — **verified single-argument**; the
  id-carrying variant `draw_ir_v2_to_v3_with_ids(composition, scene_id: u32, generation: u32)`
  is at line 512 and is NOT needed). This yields a scene **value**, which is what
  `present_scene(scene: DrawIrV3Scene)` needs, **with no scene_id / generation / theme-snapshot
  plumbing** — so nothing extra crosses the `ScreenHost` trait. If a host later needs stable
  scene ids it calls `_with_ids` inside its own impl.
- **Packed writer path (existing, left alone):** `GuiPackedProducer`
  (`ui_gui_packed_producer.spl:303`) `impl UiPackedProducer` — `count()`/`emit()` write into
  `DrawIrV3Writer`/`UiOwnerWriter` ranges; `_gui_build_scene` (line 101) returns
  `GuiPackedScene`, **not** `DrawIrV3Scene`. Same for `WebPackedProducer`
  (`ui_web_packed_producer.spl:284`), whose `_web_build_scene(html, w, h, host_parent_id)`
  (line 78) **does** return `DrawIrV3Scene`.

Rule: `ScreenHost.present_scene` takes the **value**. A host that internally wants the packed
protocol converts inside its own impl. `showcase_core` never sees a writer.

### 0.6 `WidgetNode` is a HANDLE over module-global stores

`src/lib/common/ui/widget_store_ops.spl:5-6`:
```
struct WidgetNode:
    id: text
```
Backed by module-global `_widget_registry: [WidgetRecord]` and
`_widget_props_store: [WidgetProp]` (widget_store_ops.spl:19-20), with
`get_widget`/`upsert_widget_record`/`register_widget_child`/`get_internal_prop`/
`set_internal_prop` (lines 108, 54, 114, 138, 149) and `widget_store_revision()` (line 26).

**Four consequences, all load-bearing:**
1. Do NOT describe `showcase_core` as "pure". Correct wording: **"no I/O and no host
   imports; store-backed."** It mutates the global widget registry.
2. Two specs building the tree in one process **collide on the global registry**. Every
   SSpec example MUST use a distinct id prefix (§8.1). This repo has a documented history
   of vacuous specs; the isolation is non-negotiable.
3. Scroll state lives in a **string prop**: `widget_hit.spl:148` reads
   `_prop_int_of(node, "scroll_offset")`, line 153 writes
   `node.set_prop("scroll_offset", "{offset}")`. This is the linked-panel sync channel.
4. `widget_dispatch_key(focused_id: text, key: text)` (`widget_hit.spl:311`) takes a
   **focus id, not a root**. The host loop must carry `UIState.focused_id`
   (`widget.spl:210-213`).

### 0.7 There is no toolbar/scrollbar module — they are `WidgetKind` variants + builders

`src/lib/common/ui/widget_kind.spl` (43 variants) has `Panel:4`, `Text:5`, `List:6`,
`Menubar:9`, `Statusbar:10`, `Tabs:12`, `Button:13`, `Textfield:17`, `Scroll:24`,
`Textarea:25`, `Label:27`, `Sidebar:35`, `CommandBar:36`, `UtilityRail:43`.

`src/lib/common/ui/builder.spl` has builders for `panel:55`, `label:74`, `text_input:80`,
`button:87`, `menubar:200`, `menubar_rich:227`, `statusbar:234`, `tabs:241`, `sidebar:311`,
`scroll:373`, `textarea:385`, `column:31`, `row:39`, `text_widget:68`,
`build_tree_with_title:401`.

**There is NO `command_bar` / `utility_rail` / `toolbar` builder.** B2 uses `menubar(id, items)`
as the toolbar widget (kind `Menubar`) — **no new builder is added**, keeping `builder.spl`
out of WS-B's write set entirely. If a future task wants `CommandBar`, it gets its own
owner row.

Scrollbar is not a widget: it is drag behaviour on a `Scroll` node, via
`widget_scrollbar_pointer_down:171` / `_move:218` / `_up:258` (`widget_hit.spl`), and
scrollbar geometry is emitted by `widget_draw_ir.spl` `_build_scroll_batch:314` /
`_scroll_content_height:153`.

### 0.8 Other verified anchors

- `UIEvent` (`widget.spl:42+`) is semantic and **lossy** for ingress:
  `MouseEvent(x: f64, y: f64, button: text, kind: text)`, `ScrollEvent(x: f64, y: f64, dx: f64, dy: f64)`,
  `KeyPress(key: text)`, `Resize(width: i32, height: i32)`. f64 coords + text button vs the
  i32/i32 the widget layer actually wants. This is why `HostInputEvent` must be a new type.
- `GuiRenderer` (`src/lib/nogc_sync_mut/ui/gui_renderer.spl`), used at
  `src/app/browser/gui_window.spl:31` `g.present_argb_u32(width.to_i64(), height.to_i64(), pixels)`
  and line 38 `g.poll_event()`, with `GUI_EVT_CLOSE` imported at line 17.
- WM contract env keys (`wm_app_process_contract.spl:35-41`): `SIMPLE_WM_APP_MODE`,
  `SIMPLE_WM_BRIDGE_FILE`, `SIMPLE_WM_FRAME_FILE`, `SIMPLE_WM_EVENT_FILE`,
  `SIMPLE_WM_FRAME_SEQ_FILE`, `SIMPLE_WM_CLIENT_HOLD`; path helpers
  `wm_widget_showcase_event_path:105`, `wm_widget_showcase_frame_seq_path:108`,
  `wm_fs_app_event_seq_path:111`, `wm_fs_frame_receipt_path:114`.
- Showcase identity consts are **duplicated** in two files: `wm_app_process_contract.spl:43-63`
  (`WIDGET_SHOWCASE_APP_SOURCE`, `..._WINDOW_W: 528`, `..._WINDOW_H: 692`, etc.) and
  `showcase_catalog.spl:24-27`. Both name
  `examples/06_io/ui/widget_showcase_gui.spl`. Migration must update both — ownership in §9.
- `examples/06_io/ui/widget_showcase_gui.spl` is **1,234 lines** of hand-drawn engine2d
  primitives, bypassing the shared pipeline.
- `arch {}` block syntax (parsed by `src/app/cli/arch_check.spl:113 _parse_arch_block`), live
  example `src/compiler/85.mdsoc/adapters/__init__.spl`:
  ```
  arch {
    tier = "full"
    dimension = "adapter"
    layer = "infra"

    imports {
      allow = [
        "compiler/feature/**",
        "shared/**"
      ]
      deny = []
    }
  }
  ```

---

## B0 — Ground-truth reconciliation (blocking, tiny) — **opus**

**Objective.** Land the corrections in §0 into the design doc + lane state before any code,
so parallel agents don't re-derive them.

**Files owned (exclusive).**
- `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` (§1 "7 targets"
  → 8, enumerated; §2.3 note that `ShowcaseSurface` needs new variants; §2.2 note that
  `ScreenHost` is additive)
- `doc/08_tracking/bug/ui_backend_factory_module_missing_2026-08-06.md` (new)

**Concrete content of the bug file.** Title: `common.ui.backend_factory` imported by 7 specs
but the module does not exist. Body: the file list from §0.2, the `ls`/`grep` evidence, the
"unresolved `use` is only a WARN → fail-open" mechanism, and the verdict that those specs
provide zero backend coverage. Status OPEN, owner: outside WS-B.

**Acceptance check.**
```
grep -c '^use common\.ui\.backend' $(git ls-files 'src/**/*.spl') | ...   # documented as 8
bin/simple bug-add --id=ui_backend_factory_module_missing_2026-08-06
```
Expected: design doc no longer says "7 targets"; bug file exists and is listed by
`bin/simple bug-gen`.

**Dependencies.** none. **Blocks.** nothing hard, but B1 should read it.

---

## B1 — `ScreenHost` + `HostInputEvent` (interface design) — **opus** — BLOCKS B2..B6

**Objective.** One host interface + one input ingress type. Additive to `RenderBackend`.

**Files owned (exclusive).**
- `src/lib/common/ui/screen_host.spl` (NEW — the trait)
- `src/lib/common/ui/host_input_event.spl` (NEW — the ingress type; **sole definition site
  in the repo**)
- `src/lib/common/ui/backend.spl` (EDIT — doc comment only: point `RenderBackend` at
  `ScreenHost` as the DrawIrV3 seam; **no signature change, no deletion**)
- `src/lib/common/ui/wm_app_process_contract.spl` (EDIT — `WmFsAppEvent` field extension
  ONLY, per §0.4; B1 is the only task that edits this struct)
- `test/01_unit/lib/common/ui/host_input_event_spec.spl` (NEW)

**Not owned:** anything under `src/os/**`, `src/app/**`, `builder.spl`, `showcase_catalog.spl`.

### 1.1 `host_input_event.spl` — exact definition

```simple
# Single host->widget input ingress type. SOLE definition site.
# Replaces: UIEvent.MouseEvent/ScrollEvent for INGRESS (UIEvent stays for
# semantic app events), and the two incompatible driver-side MouseEvent types
# (WS-C converges onto this).

val HOST_BTN_NONE: i64 = 0
val HOST_BTN_LEFT: i64 = 1
val HOST_BTN_RIGHT: i64 = 2
val HOST_BTN_MIDDLE: i64 = 3

val HOST_MOD_SHIFT: i64 = 1
val HOST_MOD_CTRL: i64 = 2
val HOST_MOD_ALT: i64 = 4
val HOST_MOD_META: i64 = 8

enum HostInputEvent:
    Pointer(x: i32, y: i32, button: i64, pressed: bool, wheel: i32)
    Key(code: i64, ch: text, down: bool, mods: i64)
    Resize(w: i32, h: i32)

# --- Constructors (keep call sites from mis-ordering 5 positional args) ---
fn host_pointer_down(x: i32, y: i32, button: i64) -> HostInputEvent
fn host_pointer_up(x: i32, y: i32, button: i64) -> HostInputEvent
fn host_pointer_move(x: i32, y: i32) -> HostInputEvent        # button NONE, pressed false
fn host_pointer_wheel(x: i32, y: i32, wheel: i32) -> HostInputEvent
fn host_key_down(code: i64, ch: text, mods: i64) -> HostInputEvent
fn host_key_up(code: i64, ch: text, mods: i64) -> HostInputEvent

# --- Lossy-seam adapters (B1 OWNS these; WS-C must not redefine) ---
fn host_input_from_ui_event(ev: UIEvent) -> HostInputEvent?   # f64->i32 trunc, text->i64 btn
fn host_input_to_ui_event(ev: HostInputEvent) -> UIEvent?     # for legacy RenderBackend users
fn host_input_from_wm_fs_event(ev: WmFsAppEvent) -> HostInputEvent?
```

**Why ONE type.** Today there are three ingress models and two incompatible `MouseEvent`
structs (design doc §1 Input; `src/os/compositor/compositor.spl:6-13` carries the warning
in a comment). `UIEvent.MouseEvent` uses `x: f64, y: f64, button: text`; the widget layer
consumes `i32, i32` (`widget_dispatch_click(root, w, h, px: i32, py: i32, layout)`
— `widget_hit.spl:93`). Every backend today does its own f64→i32 + text→enum conversion at
its own call site, so each backend can (and does) diverge on rounding, button naming, and
wheel sign. `HostInputEvent` makes the conversion happen exactly once, in B1-owned code.

**Encoding notes.** `button` and `mods` are `i64`, not enums: enum payload sub-patterns and
`Dict`-of-enum are known-hazardous in this repo, and `i64` crosses the WM file bridge and
the C/PS-2 driver boundary without an ABI question. `ch: text` (not a char) because the
WM bridge and IME path are both text-shaped; empty `""` means "no printable character".
`wheel` is `i32` notches, positive = content scrolls down, matching the sign of `dy` in
`widget_dispatch_scroll(root, w, h, px, py, dy)` (`widget_hit.spl:120`).

### 1.2 `screen_host.spl` — exact trait

```simple
use common.ui.draw_ir_v3.{DrawIrV3Scene}
use common.ui.host_input_event.{HostInputEvent}

trait ScreenHost:
    fn host_name() -> text                       # "2d" | "gui" | "web" | "wm"
    fn size() -> (i32, i32)
    fn present_scene(scene: DrawIrV3Scene) -> bool
    fn poll_input() -> HostInputEvent?
    fn shutdown()
```

Five methods, no more. `init` is the impl's constructor (a `static fn open(...)`), not a
trait method — a trait `init()` with no receiver cannot carry per-host config.
`present_scene` returns `bool` (false = host closed / present failed) so the shared loop has
a termination signal without a second method.

### 1.3 Relation to `RenderBackend`: **extends by addition, replaces nothing**

`ScreenHost` is a **new, separate trait**. `RenderBackend` (`backend.spl:23`) is:
- never `impl`'d (verified — zero `impl RenderBackend for` in the tree),
- semantically a *different* contract: it renders `UIState` to a target and emits
  `render_html(UIState) -> text` (a string/HTML contract), which per the design doc's key
  constraint is the `app.ui.render`-adjacent seam we must NOT build on.

Migration for the 8 importers: **all 8 keep their import unchanged** (§0.1 table). Six are
`src/app/ui.*` shells that never implemented it anyway; two are `src/os/compositor/*` and are
outside WS-B's write boundary. Deleting `RenderBackend` is a follow-up for whoever owns the
`ui.*` consolidation — filed as a note in B0's design-doc edit, not done here. Rationale:
touching `src/os/compositor/fb_backend.spl` or `browser_backend.spl` from WS-B would collide
head-on with WS-A (backend factory) and WS-C (input backends).

### 1.4 The shared loop (lives in B2's `showcase_core`, signature fixed by B1)

```simple
fn showcase_run(host: ScreenHost, max_frames: i64) -> ShowcaseRunReport:
    var st = showcase_build()                      # UIState, store-backed
    var frames = 0
    while frames < max_frames:
        val (w, h) = host.size()
        val comp = widget_tree_to_draw_ir_cpu(st.tree.root_node(), w, h)
        val scene = draw_ir_v2_to_v3(comp, ...)
        if not host.present_scene(scene): break
        frames = frames + 1
        var ev = host.poll_input()
        while ev != nil:
            st = showcase_apply(st, ev!, w, h)      # ALL logic here; host-agnostic
            ev = host.poll_input()
    showcase_report(st, frames)
```

Note `widget_dispatch_key` needs `st.focused_id` (§0.6.4), which is why `showcase_apply`
takes and returns `UIState` rather than just the root node.

**Acceptance check.**
```
bin/simple lint src/lib/common/ui/screen_host.spl src/lib/common/ui/host_input_event.spl \
                src/lib/common/ui/wm_app_process_contract.spl
bin/simple test test/01_unit/lib/common/ui/host_input_event_spec.spl
```
Expected: lint clean; spec verdict line reports **≥ 12 examples passed, 0 failed** covering:
each constructor's field values; `host_input_from_ui_event(UIEvent.MouseEvent(3.7, 4.2, "left", "down"))`
== `Pointer(3, 4, HOST_BTN_LEFT, true, 0)`; unknown button text → `HOST_BTN_NONE`;
`host_input_from_wm_fs_event` round-trip incl. the new `ch`/`key_code` fields; wheel sign
matches `widget_dispatch_scroll` dy sign. Plus:
```
grep -rn 'enum HostInputEvent' src/ | wc -l    # expected: 1
```

**Dependencies.** B0 (soft). **Blocks.** B2, B3, B4, B5, B6 (hard), and WS-C C1.

### 1.5 WS-B / WS-C boundary — state verbatim, do not renegotiate

- **B1 lands `src/lib/common/ui/host_input_event.spl` as the SOLE definition site.**
  WS-C consumes it and never redefines `HostInputEvent`, `HOST_BTN_*`, or `HOST_MOD_*`.
- **WS-B touches NO file under `src/os/**`.** WS-C owns `src/os/drivers/input/input_event.spl`,
  `src/os/compositor/input_backend.spl`, `src/os/compositor/compositor.spl`, and the deletion
  of the duplicate driver-side `MouseEvent`.
- **The lossy `UIEvent` ↔ `HostInputEvent` conversion is B1-owned** (`host_input_from_ui_event`
  / `host_input_to_ui_event`, §1.1). WS-C calls them; WS-C does not write its own.
- **`WmFsAppEvent` field extension is B1-owned** (§0.4). WS-C and B6 consume the new fields.
- If WS-C needs a new variant or field, it files a request against B1's file; it does not
  add one. Concurrent edits to `host_input_event.spl` from two workstreams is exactly the
  clobber pattern this repo has been bitten by.

---

## B2 — `showcase_core.spl` (the shared logic) — **sonnet**

**Objective.** One store-backed module producing the showcase tree + the event reducer.
Byte-identical across all four targets. No I/O, no host imports.

**Files owned (exclusive).**
- `src/app/ui_showcase/showcase_core.spl` (NEW)
- `src/app/ui_showcase/__init__.spl` (NEW — carries the STRICT `arch {}` block, see B7)
- `test/01_unit/app/ui_showcase/showcase_core_spec.spl` (NEW)

> **Directory split (see B7 §7.1).** `showcase_core.spl` lives in
> `src/app/ui_showcase/`; ALL four host impls and mains live one level down in
> `src/app/ui_showcase/hosts/`. This is not cosmetic — one directory cannot both
> deny `engine2d`/`nogc_sync_mut.ui` and contain the files that must import them,
> because `arch_check` applies an `__init__.spl` rule to every file in its module
> (`_module_path_from_init_file:188`).

**Not owned:** `builder.spl` (§0.7 — we use `menubar` as-is), `widget_hit.spl`,
`showcase_catalog.spl`, any `main_*.spl`.

### 2.1 Allowed imports (enforced by B7)

```simple
use common.ui.builder.{column, row, panel, label, button, menubar, statusbar, scroll,
                       text_input, build_tree_with_title}
use common.ui.widget.{UITree, UIState, WidgetRect}
use common.ui.widget_store_ops.{WidgetNode, get_internal_prop, set_internal_prop}
use common.ui.widget_hit.{widget_dispatch_click, widget_dispatch_scroll, widget_dispatch_key,
                          widget_scrollbar_pointer_down, widget_scrollbar_pointer_move,
                          widget_scrollbar_pointer_up, widget_hit_test}
use common.ui.layout.{compute_layout}
use common.ui.widget_draw_ir.{widget_tree_to_draw_ir_cpu}
use common.ui.draw_ir_v2_to_v3.{draw_ir_v2_to_v3}
use common.ui.draw_ir_v3.{DrawIrV3Scene}
use common.ui.screen_host.{ScreenHost}
use common.ui.host_input_event.{HostInputEvent, HOST_BTN_LEFT}
```
No `engine2d`, no `gui_renderer`, no `std.fs`, no `std.env`, no `src/os/**`.

### 2.2 Widget tree — real `WidgetKind` variants only

```simple
val SC: text = "sc"          # id prefix; every id is "{prefix}_..." so specs can isolate

fn showcase_build(prefix: text) -> UIState:
    val toolbar = menubar("{prefix}_toolbar",
        ["New", "Open", "Sync", "Probe", "Quit"])                       # kind Menubar

    val left = scroll("{prefix}_panel_left", 240, _rows(prefix, "L", 40))   # kind Scroll
    val right = scroll("{prefix}_panel_right", 240, _rows(prefix, "R", 40)) # kind Scroll
    val linked = row("{prefix}_linked", [left, right])

    val free = scroll("{prefix}_panel_free", 160, _rows(prefix, "F", 30))   # unlinked control

    val probe = panel("{prefix}_probe", "Event Probe", [
        label("{prefix}_probe_last",  "last: -"),
        label("{prefix}_probe_click", "clicks: 0"),
        label("{prefix}_probe_drag",  "drag: -"),
        label("{prefix}_probe_keys",  "typed: "),
        text_input("{prefix}_probe_input", "type here")                 # kind Textfield
    ])

    val win_a = panel("{prefix}_win_a", "Window A", [label("{prefix}_win_a_body", "alpha")])
    val win_b = panel("{prefix}_win_b", "Window B", [label("{prefix}_win_b_body", "beta")])
    val windows = row("{prefix}_windows", [win_a, win_b])

    val status = statusbar("{prefix}_status", "ready", "0 events")      # kind Statusbar
    val root = column("{prefix}_root", [toolbar, linked, free, windows, probe, status])
    UIState.new(build_tree_with_title(root, "Simple Showcase", "glass_dark"))
```

`_rows(prefix, tag, n)` emits `n` `label("{prefix}_{tag}{i}", "{tag} row {i}")` so both
scroll panels overflow their 240px viewport and a scrollbar is emitted by
`_build_scroll_batch` (`widget_draw_ir.spl:314`).

**Toolbar = `menubar`** (§0.7). No new builder; `builder.spl` stays out of the write set.
**Windows** are `panel` nodes here — real OS windows appear only on the WM host (B6), where
the same tree is what the WM window contains. `Scroll` gets its scrollbar behaviour free
from `widget_scrollbar_pointer_*`; there is no scrollbar widget to construct.

### 2.3 Linked-panel scroll sync — post-dispatch, in `showcase_core`

`widget_hit.spl` is NOT modified. Scroll offset is a string prop (§0.6.3), so sync is a read
of the source's prop and a write to the destination's, immediately after dispatch:

```simple
val LINK_SRC: text = "_panel_left"
val LINK_DST: text = "_panel_right"

# Replicates widget_hit.spl:356 `_prop_int_of` EXACTLY. That fn is private, so
# showcase_core cannot call it; B2 copies the verified body rather than inventing
# a cast. Do NOT write `raw.to_i64().to_i32()` — chained .to_i64() on a method
# result returns garbage under JIT in this repo (known defect). `.to_int() ?? 0`
# is the idiom widget_hit itself uses.
fn _scroll_offset(n: WidgetNode) -> i32:
    val raw = n.get_prop("scroll_offset")
    if raw == "":
        return 0
    raw.to_int() ?? 0

fn _sync_linked(prefix: text):
    """Mirror left panel's committed scroll_offset onto the right panel.
    Runs AFTER widget_dispatch_scroll / widget_scrollbar_pointer_move have
    clamped the source (widget_hit.spl:148-153, :208-213, :252), so the
    mirrored value is always already within range for an identically-sized
    panel. One-directional by design: left drives right."""
    val src = WidgetNode(id: "{prefix}{LINK_SRC}")
    val dst = WidgetNode(id: "{prefix}{LINK_DST}")
    val off = _scroll_offset(src)
    if _scroll_offset(dst) != off:
        dst.set_prop("scroll_offset", "{off}")
```

Called at exactly three sites in `showcase_apply`: after `widget_dispatch_scroll`, after
`widget_scrollbar_pointer_move`, after `widget_scrollbar_pointer_up`. `_panel_free` is never
synced — it is the negative control that proves the sync is a real mechanism and not a global
scroll.

### 2.4 Event reducer + visible probe pane

```simple
fn showcase_apply(st: UIState, ev: HostInputEvent, w: i32, h: i32) -> UIState:
    match ev:
        HostInputEvent.Pointer(x, y, button, pressed, wheel):
            if wheel != 0:
                widget_dispatch_scroll(st.tree.root_node(), w, h, x, y, wheel * 24)
                _sync_linked(st_prefix(st))
                _probe(st, "wheel {wheel} @{x},{y}")
            else if pressed and button == HOST_BTN_LEFT:
                _set_drag_anchor(st, x, y)
                if not widget_scrollbar_pointer_down(st.tree.root_node(), w, h, x, y):
                    val hit = widget_dispatch_click(st.tree.root_node(), w, h, x, y,
                                                    compute_layout(st.tree.root_node(), w, h))
                    _bump_click(st); _probe(st, "click {hit} @{x},{y}")
                    st = _focus(st, hit)                  # feeds widget_dispatch_key
            else if not pressed:
                widget_scrollbar_pointer_up(st.tree.root_node())
                _sync_linked(st_prefix(st))
                _clear_drag_anchor(st); _probe(st, "up @{x},{y}")
            else:
                widget_scrollbar_pointer_move(st.tree.root_node(), w, h, x, y)
                _sync_linked(st_prefix(st))
                if _drag_active(st): _probe_drag(st, x, y)   # "drag: dx,dy"
        HostInputEvent.Key(code, ch, down, mods):
            if down:
                widget_dispatch_key(st.focused_id, if ch != "" then ch else _keyname(code))
                _append_typed(st, ch); _probe(st, "key '{ch}' code {code} mods {mods}")
        HostInputEvent.Resize(nw, nh):
            _probe(st, "resize {nw}x{nh}")
    st
```

`_probe`/`_bump_click`/`_probe_drag`/`_append_typed` write into the probe labels'
`"label_text"` prop, so **every event is visibly rendered** in the next frame's DrawIR —
which is what makes AC-5's screenshot evidence real and not a log-file claim. Drag is
detected as move-with-anchor (anchor set on press, cleared on release), stored in
`set_internal_prop("{prefix}_probe", "drag_anchor", "{x},{y}")`.

`showcase_report(st, frames) -> ShowcaseRunReport{host_name, frames, clicks, drags,
typed_text, left_offset, right_offset, free_offset}` — the machine-readable transcript B8
captures alongside the screenshot.

**Acceptance check.**
```
bin/simple test test/01_unit/app/ui_showcase/showcase_core_spec.spl
```
Expected verdict **≥ 10 examples, 0 failed**, each using its own `prefix` (`sc_a`, `sc_b`, …
per §0.6.2), asserting:
1. toolbar node kind == `"menubar"`; 5 items.
2. both linked scroll nodes exist with content taller than viewport.
3. `showcase_apply(Pointer wheel=+3)` over left panel → left offset > 0 **and**
   right offset == left offset **and** free offset == 0.
4. scrollbar drag (`down` → `move` → `up`) on left → right mirrors, free unchanged.
5. `Key(code, "x", true, 0)` after focusing the text input → typed text contains `"x"`.
6. probe label text changes after each of click / drag / key (the visible-log guarantee).
7. `widget_tree_to_draw_ir_cpu` → `draw_ir_v2_to_v3` yields a `DrawIrV3Scene` with a
   nonzero command count and ≥1 hit shape.

**Dependencies.** B1. **Parallel with:** B3, B4, B5, B6 are *consumers* — they depend on
B2's signatures, so B2 publishes `showcase_build`/`showcase_apply`/`showcase_run`/
`ShowcaseRunReport` signatures in this document (above) and the host tasks code against
them from day one without waiting.

---

## B3 — 2D host impl + main — **sonnet**

**Objective.** Raw framebuffer host: engine2d software surface, no window manager.

**Files owned (exclusive).**
- `src/app/ui_showcase/hosts/host_2d.spl` (NEW)
- `src/app/ui_showcase/hosts/main_2d.spl` (NEW)
- `test/03_system/ui_showcase/showcase_2d_spec.spl` (NEW)

**Shape.**
```simple
struct Screen2dHost:
    w: i32
    h: i32
    surface_handle: i64
    queue: [HostInputEvent]

impl ScreenHost for Screen2dHost:
    me host_name() -> text: "2d"
    me size() -> (i32, i32): (self.w, self.h)
    me present_scene(scene: DrawIrV3Scene) -> bool:
        # rasterize scene into the engine2d software surface, then flush.
        # scene walk stays in this file; showcase_core never sees engine2d.
    me poll_input() -> HostInputEvent?:
        # host mode: synthetic queue seeded from SIMPLE_SHOWCASE_SCRIPT
        # guest mode: drains the WS-C input queue (consumed, not defined, here)
    me shutdown()
```
`main_2d.spl`: read `SIMPLE_SHOWCASE_W/H` (default 800×600), open the host, call
`showcase_run(host, max_frames)`, print the `ShowcaseRunReport` as one line, write a PPM/PNG
of the final framebuffer to `SIMPLE_SHOWCASE_CAPTURE`.

**LOC ceiling: `host_2d.spl` ≤ 180, `main_2d.spl` ≤ 60.** If the impl exceeds this, scene-walk
logic has leaked into the host that belongs in a shared DrawIrV3 rasterizer — file it, don't
grow the host.

**Acceptance check.**
```
SIMPLE_SHOWCASE_CAPTURE=build/showcase/2d.ppm bin/simple run src/app/ui_showcase/hosts/main_2d.spl
```
Expected stdout one line `showcase host=2d frames=N clicks=.. drags=.. typed=".." left=K right=K free=0`
with `left == right` and `free == 0`; `build/showcase/2d.ppm` exists and is **nonblank**
(≥2 distinct pixel values). Blank framebuffer = FAIL, not a pass.

**Dependencies.** B1, B2 signatures. **Note:** real driver-origin input on 2D is WS-C's C5;
B3 delivers the host + the script-driven path.

---

## B4 — GUI host impl + main + migration of `widget_showcase_gui.spl` — **sonnet**

**Objective.** SDL2/winit window host via `GuiRenderer`; retire the 1,234-line hand-drawn example.

**Files owned (exclusive).**
- `src/app/ui_showcase/hosts/host_gui.spl` (NEW)
- `src/app/ui_showcase/hosts/main_gui.spl` (NEW)
- `examples/06_io/ui/widget_showcase_gui.spl` (REWRITE — see B4.2)
- `test/03_system/ui_showcase/showcase_gui_spec.spl` (NEW)

**B4.1 Host.** Wraps `GuiRenderer` exactly as `src/app/browser/gui_window.spl:31,38` does:
```simple
impl ScreenHost for ScreenGuiHost:
    me host_name() -> text: "gui"
    me present_scene(scene: DrawIrV3Scene) -> bool:
        val px = _raster_argb(scene, self.w, self.h)          # -> [u32]
        self.g.present_argb_u32(self.w.to_i64(), self.h.to_i64(), px)
    me poll_input() -> HostInputEvent?:
        val ev = self.g.poll_event()                          # GuiRenderer event
        if ev == GUI_EVT_CLOSE: self.closed = true; return nil
        _gui_event_to_host(ev)                                # -> HostInputEvent
```
`_gui_event_to_host` is the only GUI-specific translation and lives here.

**B4.2 Migration.** `examples/06_io/ui/widget_showcase_gui.spl` shrinks from 1,234 lines to a
**≤ 30-line shim**. `use app.*` from `examples/` is **verified to resolve** —
`examples/06_io/ui/demo_scroll_textarea.spl:13` already does
`use app.ui.tui.screen.{Screen}`:
```simple
use app.ui_showcase.showcase_core.{showcase_run}
use app.ui_showcase.hosts.host_gui.{ScreenGuiHost}

fn main():
    val host = ScreenGuiHost.open(528, 692)     # WIDGET_SHOWCASE_WINDOW_W/H
    println(showcase_run(host, _frames_from_env()).line())
```
Window size 528×692 is kept to match `WIDGET_SHOWCASE_WINDOW_W/H`
(`wm_app_process_contract.spl:47-48`) so existing WM launch expectations still hold.
**All hand-drawn engine2d primitive calls are deleted, not commented out.**

Known trap: `fn main` in a file makes `run` drop `describe`/`it` blocks — the example keeps
`fn main` and carries no spec blocks; its coverage is `test/03_system/ui_showcase/showcase_gui_spec.spl`.

**LOC ceiling: `host_gui.spl` ≤ 180, `main_gui.spl` ≤ 60, migrated example ≤ 30.**

**Acceptance check.**
```
wc -l examples/06_io/ui/widget_showcase_gui.spl                 # expect <= 30
grep -c 'engine2d' examples/06_io/ui/widget_showcase_gui.spl    # expect 0
bin/simple run examples/06_io/ui/widget_showcase_gui.spl        # see positive check below
```
**Positive check, not a negative one.** The two greps above are satisfied by a shim whose
`use` lines silently fail to resolve — an unresolved `use` is only a WARN (§0.2), so a
do-nothing shim would score `≤30 lines` and `0 engine2d` while rendering nothing. The
binding assertion is therefore on **stdout**: the run must print the
`showcase host=gui frames=N clicks=.. ...` line with **N > 0**. Zero frames, no line, or a
line with `frames=0` is a FAIL. Also assert the run emits no
`unresolved`/`unknown module` warning on stderr.

Plus B8's `play_sdl2_screenshot` artifact.

**Dependencies.** B1, B2 signatures.

---

## B5 — Web host impl + main — **sonnet**

**Objective.** Serve the same scene through the ui.web server path.

**Files owned (exclusive).**
- `src/app/ui_showcase/hosts/host_web.spl` (NEW)
- `src/app/ui_showcase/hosts/main_web.spl` (NEW)
- `test/03_system/ui_showcase/showcase_web_spec.spl` (NEW)

**Not owned:** `src/app/ui.web/server.spl`, `src/app/ui.web/backend.spl`,
`src/lib/common/ui/ui_web_packed_producer.spl` — B5 **calls** them, edits none.

**Shape.** `present_scene` holds the latest `DrawIrV3Scene` and renders it for the HTTP
client; where the web lane needs the packed form it uses `WebPackedProducer`
(`ui_web_packed_producer.spl:284`) whose `_web_build_scene(html, w, h, host_parent_id)`
(line 78) already returns `DrawIrV3Scene` (§0.5). `poll_input` drains browser-posted events
through the ui.web server's existing event endpoint, converted by `_web_event_to_host`.
Internal window widget / scrollpane+bar come from the shared tree — no web-specific widgets.

**LOC ceiling: `host_web.spl` ≤ 200 (HTTP plumbing), `main_web.spl` ≤ 60.**

**Acceptance check.**
```
SIMPLE_SHOWCASE_PORT=8791 bin/simple run src/app/ui_showcase/hosts/main_web.spl &
# then B8's play_ui_snapshot against the served page
```
Expected: served page contains the toolbar's 5 item labels and both linked panels; posting a
wheel event to the left panel and re-snapshotting shows both panels' first visible row
changed identically while the free panel's did not.

**Dependencies.** B1, B2 signatures.

---

## B6 — WM host impl + main — **sonnet**

**Objective.** Run the same showcase as a WM client process over the file/env bridge.

**Files owned (exclusive).**
- `src/app/ui_showcase/hosts/host_wm.spl` (NEW)
- `src/app/ui_showcase/hosts/main_wm.spl` (NEW)
- `test/03_system/ui_showcase/showcase_wm_spec.spl` (NEW)

**Not owned:** `src/lib/common/ui/wm_app_process_contract.spl` (B1 owns the struct edit;
B6 only reads/uses the consts and helpers), `src/app/wm_showcase/**` (existing app; B6
**learns from** `main.spl:8`/`run.spl`/`session.spl`/`capture_artifact.spl` and copies the
launch/capture pattern, editing none of them).

**Shape.** Client mode gated on `WM_APP_MODE_ENV == WM_APP_MODE_CLIENT`
(`wm_app_process_contract.spl:35-36`, `wm_app_mode_is_client:90`):
- `size()` → `WIDGET_SHOWCASE_WINDOW_W/H` (528×692, lines 47-48).
- `present_scene` → rasterize to ARGB, write to `WM_FRAME_FILE_ENV` path, bump
  `WM_FRAME_SEQ_FILE_ENV` via `wm_widget_showcase_frame_seq_path:108`, emit the
  `WmFsFrameReceipt` (struct at line 25) at `wm_fs_frame_receipt_path:114`.
- `poll_input` → read the next `WmFsAppEvent` from `wm_fs_app_event_seq_path(event_path, seq)`
  (line 111) and convert with B1's `host_input_from_wm_fs_event`.
- Window title from `showcase_window_title(prefix, backend)` (line 87).

**Depends on B1's `WmFsAppEvent` extension (§0.4).** Until those fields land, keytype on WM
is impossible — B6 must NOT claim AC-5 keytype without them, and must NOT add the fields
itself.

**LOC ceiling: `host_wm.spl` ≤ 200 (file bridge + receipt), `main_wm.spl` ≤ 60.**

**Acceptance check.** B8's `play_wm_screenshot` + `play_wm_click` + `play_wm_type` sequence;
plus a frame receipt with nonzero `pixel_count` and `checksum`.

**Dependencies.** B1 (hard, incl. §0.4), B2 signatures.

---

## B7 — Architecture dependency check — **sonnet**

**Objective.** Prove mechanically that showcase modules import only common/ui + `ScreenHost`,
and that engine2d / SDL / `src/os/**` imports appear ONLY in `host_*.spl`.

**Files owned (exclusive).**
- `src/app/ui_showcase/__init__.spl` — **the STRICT `arch {}` block** (B2 creates the file;
  B7 owns the arch block content; sequence B2 → B7 so there is no concurrent write)
- `src/app/ui_showcase/hosts/__init__.spl` — **the PERMISSIVE `arch {}` block** (NEW, B7)
- `scripts/check/check-ui-showcase-arch.shs` (NEW)
- `test/01_unit/app/ui_showcase/showcase_arch_spec.spl` (NEW)

**Mechanism.** `src/app/cli/arch_check.spl` scans `__init__.spl` for `arch {}` blocks
(`_parse_arch_block:113`), derives the module path from the `__init__.spl` location
(`_module_path_from_init_file:188`), collects `use` statements
(`_parse_imports_from_content:334`), and reports `ArchViolation` (struct at line 29) against
allow/deny globs (`_arch_explicitly_allows:250`). Live syntax example:
`src/compiler/85.mdsoc/adapters/__init__.spl` (quoted in §0.8).

### 7.1 Why two directories, not one

A rule attached to an `__init__.spl` applies to **every file in that module**. A single
`src/app/ui_showcase/` directory therefore cannot simultaneously (a) deny `engine2d` /
`nogc_sync_mut.ui` — which is the entire point of AC-3 — and (b) contain `host_gui.spl`,
which *must* import `nogc_sync_mut.ui.gui_renderer`, and `host_2d.spl`, which *must* import
engine2d. The deny rule would fire on the hosts. Splitting the module is what makes the arch
block the real enforcement mechanism instead of a rule that has to be disabled to compile:

```
src/app/ui_showcase/            __init__.spl = STRICT   -> showcase_core.spl
src/app/ui_showcase/hosts/      __init__.spl = PERMISSIVE -> host_*.spl, main_*.spl
```

**STRICT — `src/app/ui_showcase/__init__.spl`:**
```
arch {
  tier = "full"
  dimension = "app"
  layer = "ui"

  imports {
    allow = [
      "common/ui/**",
      "std/**"
    ]
    deny = [
      "**/engine2d/**",
      "nogc_sync_mut/ui/**",
      "os/**",
      "app/browser/**",
      "app/ui_showcase/hosts/**"
    ]
  }
}
```
The last deny is the one that keeps the dependency arrow pointing the right way:
`showcase_core` must never import a host. Hosts import core, never the reverse.

**PERMISSIVE — `src/app/ui_showcase/hosts/__init__.spl`:**
```
arch {
  tier = "full"
  dimension = "adapter"
  layer = "infra"

  imports {
    allow = [
      "common/ui/**",
      "app/ui_showcase/**",
      "nogc_sync_mut/ui/**",
      "gc_async_mut/gpu/engine2d/**",
      "app/ui.web/**",
      "std/**"
    ]
    deny = [
      "os/**"
    ]
  }
}
```
`os/**` stays denied even for hosts — §1.5's WS-B/WS-C boundary is mechanically enforced,
not merely stated.

### 7.2 The guard script

The arch block above is now the primary check. `check-ui-showcase-arch.shs` runs it and adds
one rule the glob syntax cannot express — that `showcase_core.spl` is the *only* file in the
strict module, so nobody can smuggle a host in beside it:

```sh
# 1. arch rules (primary)
bin/simple check-arch --root src/app/ui_showcase || { echo "FAIL — arch violation"; exit 1; }

# 2. strict module contains only host-free files
STRAY=$(grep -ln 'engine2d\|gui_renderer\|^use os\.\|^use app\.ui_showcase\.hosts' \
          src/app/ui_showcase/*.spl 2>/dev/null)
[ -z "$STRAY" ] || { echo "FAIL — host-only import in strict module: $STRAY"; exit 1; }

N=$(ls src/app/ui_showcase/*.spl src/app/ui_showcase/hosts/*.spl 2>/dev/null | wc -l)
[ "$N" -gt 0 ] || { echo "ERROR — nothing was checked"; exit 2; }
echo "PASS — $N showcase file(s) checked"
```

**Fail-closed requirement.** Per this repo's guard convention, the script's LAST stdout line
is a verdict: `PASS — <n> file(s) checked` (n>0, exit 0), `FAIL — ...` (exit 1), or
`ERROR — nothing was checked` (exit 2). A run that globs zero files is an ERROR, never a pass
— that is precisely the fail-open pattern that has burned this repo before. Ship two fixtures
under `test/fixtures/arch_check/` (one clean, one with an engine2d import in
`showcase_core.spl`) and assert the guard's own selftest catches the dirty one.

**Acceptance check.**
```
sh scripts/check/check-ui-showcase-arch.shs
```
Expected last line `PASS — 7 file(s) checked` (or current n>0). Negative proof: temporarily
add `use gc_async_mut.gpu.engine2d.scene` to `showcase_core.spl` → last line starts `FAIL —`,
exit 1. Both directions must be demonstrated in the task's evidence.

**Dependencies.** B2 (file exists) + B3..B6 (hosts exist to be classified).

---

## B8 — Evidence capture + readiness bits — **sonnet**

**Objective.** One captured artifact per target; readiness bits flip ONLY with an artifact.

**Files owned (exclusive).**
- `src/lib/common/ui/showcase_catalog.spl` (**sole owner** — schema change AND bit flips AND
  source-path updates; no other task edits it)
- `scripts/check/check-ui-showcase-evidence.shs` (NEW)
- `doc/09_report/ui_showcase_screenhost_evidence_2026-08-06.md` (NEW)
- `test/01_unit/lib/common/ui/showcase_catalog_spec.spl` (EDIT/NEW)

### 8.1 Tool per target — real MCP tools available in this repo

| Target | Launch | Interaction | Capture | Artifact |
|--------|--------|-------------|---------|----------|
| **wm** | `main_wm.spl` in WM client mode | `play_wm_click`, `play_wm_type` | `play_wm_screenshot` | `doc/09_report/artifacts/showcase_wm.png` + report line |
| **gui** | `main_gui.spl` (SDL2) | `play_sdl2_click` (+ `play_sdl2_state` to confirm the window) | `play_sdl2_screenshot` | `showcase_gui.png` + report line |
| **web** | `main_web.spl` + ui.web server | `play_ui_act` via `play_ui_connect` | `play_ui_snapshot` | `showcase_web.json` snapshot + report line |
| **2d** | `main_2d.spl`, script-driven | scripted `HostInputEvent`s (no window to click) | direct framebuffer dump | `showcase_2d.ppm` + report line |

Sequence for each target (this is the AC-5 transcript):
1. click the toolbar → probe pane shows `click <toolbar-item-id>`;
2. drag the left panel's scrollbar → probe shows `drag: dx,dy` **and** the right panel's rows
   shift identically while the free panel's do not (this is the linked-panel proof, visible
   in the screenshot, not just in the report line);
3. type `abc` into the probe input → probe shows `typed: abc`;
4. screenshot after each step.

### 8.2 `showcase_catalog.spl` schema change (§0.3)

```simple
enum ShowcaseSurface:
    Standalone
    HostWm
    SimpleOsWm
    Web          # NEW
    Raw2d        # NEW

struct ShowcaseEntry:
    ...
    web_ready: bool      # NEW
    raw2d_ready: bool    # NEW
```
Extend `showcase_surface_supported` (line 68) with the two new arms. Add a 4th entry
`SHARED_SHOWCASE_APP_ID = "shared_screenhost_showcase"` whose `source_path` is
`src/app/ui_showcase/hosts/main_gui.spl`, all five bits **false** at creation. Update
`GUI_WIDGET_SHOWCASE_SOURCE` (line 27) only if B4 moves the file — B4 keeps the path, so it
does not change; the duplicated const block at `wm_app_process_contract.spl:43-63` therefore
also stays valid and needs no edit (avoiding a second writer on that file).

### 8.3 The rule

`check-ui-showcase-evidence.shs` is the gate: for each `true` readiness bit in
`showcase_catalog()`, the corresponding artifact file must exist, be nonempty, be nonblank
(≥2 distinct pixel values for images), and be referenced in the report. A `true` bit with a
missing artifact is `FAIL`. Same verdict-line contract as B7 (`PASS — n bit(s) verified` /
`FAIL` / `ERROR — nothing was checked`).

**Acceptance check.**
```
sh scripts/check/check-ui-showcase-evidence.shs
bin/simple test test/01_unit/lib/common/ui/showcase_catalog_spec.spl
```
Expected: `PASS — n bit(s) verified` with n = number of flipped bits; spec asserts the two
new enum arms are reachable and that a bit-with-no-artifact is rejected.

**Dependencies.** B3, B4, B5, B6 (all four must run), B7 (arch must be clean first).

---

## 9. File ownership matrix (parallel-safety contract)

Exactly one task writes each file. Any agent finding a file it needs listed under another
task **stops and coordinates** rather than editing.

| File | Owner | Notes |
|------|-------|-------|
| `doc/05_design/.../screen_backend_selection_and_shared_showcase.md` | B0 | |
| `doc/08_tracking/bug/ui_backend_factory_module_missing_2026-08-06.md` | B0 | |
| `src/lib/common/ui/screen_host.spl` | **B1** | new |
| `src/lib/common/ui/host_input_event.spl` | **B1** | new; SOLE definition site repo-wide |
| `src/lib/common/ui/backend.spl` | **B1** | doc comment only |
| `src/lib/common/ui/wm_app_process_contract.spl` | **B1** | `WmFsAppEvent` fields only |
| `src/app/ui_showcase/showcase_core.spl` | **B2** | strict module |
| `src/app/ui_showcase/__init__.spl` | B2 creates / **B7 owns `arch {}`** | STRICT block; strictly sequential |
| `src/app/ui_showcase/hosts/__init__.spl` | **B7** | PERMISSIVE block |
| `src/app/ui_showcase/hosts/host_2d.spl`, `main_2d.spl` | **B3** | |
| `src/app/ui_showcase/hosts/host_gui.spl`, `main_gui.spl` | **B4** | |
| `examples/06_io/ui/widget_showcase_gui.spl` | **B4** | 1234 → ≤30 lines |
| `src/app/ui_showcase/hosts/host_web.spl`, `main_web.spl` | **B5** | |
| `src/app/ui_showcase/hosts/host_wm.spl`, `main_wm.spl` | **B6** | |
| `scripts/check/check-ui-showcase-arch.shs` | **B7** | |
| `src/lib/common/ui/showcase_catalog.spl` | **B8** | schema + bits + paths, all of it |
| `scripts/check/check-ui-showcase-evidence.shs` | **B8** | |
| `src/lib/common/ui/builder.spl` | **NOBODY** | §0.7 — toolbar is `menubar` |
| `src/lib/common/ui/widget_hit.spl` | **NOBODY** | §2.3 — sync is post-dispatch |
| `src/os/**` | **NOBODY in WS-B** | §1.5 — WS-C/WS-A |
| `src/app/wm_showcase/**` | **NOBODY in WS-B** | B6 reads the pattern only |
| `src/app/ui.web/**`, `ui_web_packed_producer.spl` | **NOBODY in WS-B** | B5 calls, does not edit |

Parallelism: **B0 ∥ nothing else needed** → **B1 (opus, blocking)** → **B2, B3, B4, B5, B6 in
parallel (5 sonnet agents, disjoint files)** → **B7** → **B8**. B3–B6 code against B2's
signatures as published in §1.4/§2.2/§2.4 and do not wait for B2 to land.

---

## 10. SSpec scenarios per AC

All new specs go under `test/01_unit/` and `test/03_system/`. **Not** `test/unit/` or
`test/system/` — those are legacy duplicates (both trees contain `unified_app_spec.spl`);
writing there is invisible to the current lane. Follow `.claude/skills/spipe.md` step-based
conventions and scaffold from `.claude/templates/spipe_template.spl`.

| AC | Spec path | Asserts |
|----|-----------|---------|
| AC-3 | `test/01_unit/lib/common/ui/host_input_event_spec.spl` (B1) | one `HostInputEvent` definition; constructor field values; `UIEvent`→host conversion incl. f64 truncation and unknown-button fallback; `WmFsAppEvent`→host incl. new `ch`/`key_code` |
| AC-3 | `test/01_unit/app/ui_showcase/showcase_arch_spec.spl` (B7) | clean fixture → no violations; dirty fixture (engine2d import in `showcase_core.spl`) → ≥1 `ArchViolation`; zero-file scan → ERROR not PASS |
| AC-4 | `test/01_unit/app/ui_showcase/showcase_core_spec.spl` (B2) | the 7 assertions in §2.4's acceptance check; distinct id prefix per example (§0.6.2) |
| AC-4 | `test/03_system/ui_showcase/showcase_gui_spec.spl` (B4) | migrated example is ≤30 lines, has 0 `engine2d` references, and produces the same `ShowcaseRunReport` counters as `showcase_core_spec`'s scripted run |
| AC-5 | `test/03_system/ui_showcase/showcase_2d_spec.spl` (B3) | scripted click+drag+key → report line shows clicks≥1, drags≥1, typed=="abc", left==right, free==0; capture nonblank |
| AC-5 | `test/03_system/ui_showcase/showcase_web_spec.spl` (B5) | `play_ui_snapshot` before/after wheel shows both linked panels moved identically, free unchanged |
| AC-5 | `test/03_system/ui_showcase/showcase_wm_spec.spl` (B6) | frame receipt with nonzero `pixel_count`+`checksum`; probe pane text reflects `play_wm_click`/`play_wm_type` |
| AC-10 | `test/01_unit/lib/common/ui/showcase_catalog_spec.spl` (B8) | new `Web`/`Raw2d` arms reachable via `showcase_surface_supported`; a `true` bit with a missing artifact fails the evidence gate |

**Anti-vacuity rules for every spec above** (this repo has documented 15%-vacuous corpora):
no `assert` without a comparison; no spec whose only assertion is that a function returned;
each spec's verdict line must report a **nonzero** example count and be read directly, not
inferred from exit status; specs sharing a process use distinct widget id prefixes.

---

## 11. Global gates (inherited, restated)

- Every task pushes to GH immediately on landing — per fix, not batched.
- No readiness/evidence bit flips without a captured artifact (B8's gate enforces it).
- Failing tests are never skipped. Grammar or perf issues hit during implementation are
  filed as concrete bugs, not normalized into workarounds.
- Measure with the deployed self-hosted binary. `SIMPLE_EXECUTION_MODE=native` is not a mode;
  a green run from the Rust seed does not prove the self-hosted path.
- Refresh the related LLM wiki entries (`doc/00_llm_process/feature_expert/`,
  `layer_expert/`) in the same commit as the work.
