# Web Engine: Simple Script, JS Engine, and Interactive DOM Event Parity

> Verifies end-to-end interactive DOM scripting, mutation commit, pixel re-render, and event dispatch parity across Chrome, Simple JS, and `<script type="text/simple">`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Engine: Simple Script, JS Engine, and Interactive DOM Event Parity

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_web/feature/script_js_and_events_render_parity_spec.spl` |
| Requirement | `REQ-WEB-SCRIPT-JS-EVENTS-001` |

## Scenarios

### Web engine script JS, SimpleScript, and DOM event parity

#### executes initial boot DOM mutations and renders pixels for JS and SimpleScript

- Open JS boot page (`<script>`) in `BrowserSession` and inspect `#status-pill`, `#cards`, and `console_logs()`.
  - Expected: `#status-pill` becomes `"Engine Active: 4 modules"` with `#10b981` border, `#cards` receives 4 appended elements, and `console_logs()` contains `"e01:boot:4modules"`.
- Open SimpleScript boot page (`<script type="text/simple">`) in `BrowserSession` and inspect mutated DOM.
  - Expected: Identical DOM mutations and console output via `SimpleScriptDomVm`.
- Render post-script page via `simple_web_render_html_with_scripts_to_rgba_pixels(ss_html, 160, 120)`.
  - Expected: Returns `160 * 120 * 4` RGBA software-rendered bytes reflecting script DOM mutations.

#### handles click, drag-and-drop, pointer drag, dropdown, input, hover, checkbox, and form submit parity

- `e02`: Click `#btn-count` 3 times and `#tab-perf` once.
  - Expected: `#counter-val` equals `"Clicks: 3"`, `#status-badge` equals `"Tab: Performance"`, and `#tab-perf` carries `active`.
- `e03`: Drag `#drag-card` onto `#drop-zone` with `dataTransfer`, then pointer-drag `#range-track` to `offsetX=169`.
  - Expected: `#drop-zone` becomes `"Dropped: Layer Card"` (`#22c55e` border), `#slider-label` becomes `"Slider: 65%"`, and `#range-fill` style width becomes `"65%"`.
- `e04`: Select `"emerald"` on `#theme-select`.
  - Expected: `#theme-banner` updates to `"Theme: emerald"`.
- `e05`: Set text input `"Simple2D"` on `#filter-input`.
  - Expected: `#query-preview` updates to `"Query: Simple2D (8 chars)"`.
- `e06`: Hover `#hover-tile`, click `#agree-cb`, and click submit button `#submit-btn` (`preventDefault()`).
  - Expected: `#agree-cb` is `checked`, `#submit-result` becomes `"Submitted: Checked | Hover: Active"`, and page stays loaded without navigation.

</details>
