# Web & UI System Events: Button, Dropdown, Scroll, and Internal Window Drag

> Verifies end-to-end event dispatch, state transition, capture/release semantics, and rendered HTML/pixel updates for button click, dropdown selection, clamped wheel scrolling, and internal floating window drag across Web DOM (`BrowserSession`) and UI Session (`UISession` / `render_html_tree`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web & UI System Events: Button, Dropdown, Scroll, and Internal Window Drag

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_web/feature/event_button_dropdown_scroll_window_drag_spec.spl` |
| Requirement | `REQ-WEB-SYS-EVENTS-001` |

## Scenarios

### System event handling for button, dropdown, scroll, and internal window drag

#### dispatches button, select dropdown, clamped wheel scroll, and captured window drag across JS and SimpleScript DOM

- Button: Dispatch `pointerdown`/`mousedown` then `pointerup`/`mouseup`/`click` twice at `(90, 82)` in both `<script>` JS and `<script type="text/simple">` pages.
  - Expected: `#action-btn` gains `.active` during press and `#btn-status` becomes `"Count: 2 at (90,82)"`.
- Dropdown: Call `dispatch_dom_select_index` with index `1` (`emerald`) on `#mode-select`.
  - Expected: `#mode-select` updates selected `<option>` and `value`, firing `input` and `change` listeners so `#drop-status` becomes `"Selected: emerald (#1)"`.
- Scroll: Call `dispatch_dom_wheel_at` on `#scroll-box` (`data-scroll-height='280'`, `data-client-height='120'`) with deltas `+90`, `+500`, `-400`, `+120`.
  - Expected: `scrollTop` accumulates and clamps cleanly to `[0, 160]` (`90`, `160`, `0`, `120`), firing `scroll` listeners updating `#scroll-status`, `#scroll-inner` `marginTop`, and `#scroll-mirror`.
- Internal window drag: Dispatch `mousedown` on `#win-titlebar` `(80, 52)`, `mousemove` on `#desk-canvas` `(270, 182)` outside the titlebar, `mouseup`, and an ignored follow-up `mousemove` at `(420, 310)`.
  - Expected: `#win-box` updates to `(220, 170)` via `document`/`window` listeners and ignores moves after `mouseup`.

#### routes button, dropdown popup, clamped scroll, and internal window drag through UISession and html_widgets

- Dispatch `TouchPress` on `#ui_btn` `(40, 20)` and `#ui_drop` `(40, 100)`, render `render_html_tree` while open, then click popup item `(40, 232)`.
  - Expected: `#ui_btn` enters `ui_pressed="true"`, open dropdown emits `.widget-dropdown-popup`, floating window renders `position: fixed; left: 30px; top: 180px;`, and popup click selects index `1` (`Beta`) and closes the menu.
- Dispatch `TouchPress`, `TouchMove`, `TouchRelease`, and post-release `TouchMove` against `UISession`.
  - Expected: `has_active_pointer_drag` toggles `true`/`false`, `#ui_win` moves to `(160, 210)`, and post-release moves are ignored.
- Translate wheel delta `48.0` at `(40, 200)` via `translate_wheel_event` and dispatch to `UISession`.
  - Expected: `ui_scroll` updates `scroll_offset` to `"48"`, and `render_html_tree` applies `margin-top: -48px;` and `left: 160px; top: 210px;`.

</details>
