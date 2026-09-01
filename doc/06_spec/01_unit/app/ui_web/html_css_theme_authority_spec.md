# Html Css Theme Authority Specification

> Tests covering Web CSS package authority adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Css Theme Authority Specification

## Scenarios

### Web CSS package authority adapter

#### emits a newline-delimited structural adapter before the resolved package

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a newline-delimited structural adapter before the resolved package


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a newline-delimited structural adapter before the resolved package")
val css = generate_css("aetheric_dark")
val marker = "/* Folder theme package theme=aetheric_dark"
val package_start = css.index_of(marker)
val adapter_css = css.substring(0, package_start)

expect(package_start).to_be_greater_than(0)
expect(adapter_css.contains("\\n")).to_be(false)
expect(adapter_css).to_contain("structural rules only. */\n*, *::before")
expect(css).to_contain(" */\n:root {")
expect(css).to_contain("theme=aetheric_dark")
expect(css).to_contain("--ui-traffic-close: #ff5f57")
```

</details>

#### keeps traffic-light pseudo-elements structural while the package owns paint

- keeps traffic-light pseudo-elements structural while the package owns paint


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps traffic-light pseudo-elements structural while the package owns paint")
val css = generate_css("aetheric_dark")
val marker = "/* Folder theme package theme=aetheric_dark"
val adapter_css = css.substring(0, css.index_of(marker))

expect(adapter_css).to_contain(".wm-traffic-lights button::before { content: ''; position: absolute; inset: var(--ui-traffic-dot-inset)")
expect(adapter_css).to_contain(".wm-traffic-lights button::after { content: ''; position: absolute; inset: var(--ui-traffic-glyph-inset)")
expect(adapter_css).to_contain("width: var(--ui-traffic-hit-size); height: var(--ui-traffic-hit-size)")
expect(adapter_css).to_contain(".wm-btn-close::before { background: var(--ui-traffic-close); }")
expect(adapter_css).to_contain(".wm-btn-close::after { content: var(--ui-traffic-close-glyph); }")
expect(adapter_css).to_contain(".wm-btn-minimize::after { content: var(--ui-traffic-minimize-glyph); }")
expect(adapter_css).to_contain(".wm-btn-maximize::after { content: var(--ui-traffic-maximize-glyph); }")
expect(adapter_css.contains("#ff5f57")).to_be(false)
expect(adapter_css.contains("rgba(")).to_be(false)
expect(adapter_css.contains("gradient(")).to_be(false)
expect(adapter_css.contains("blur(")).to_be(false)
expect(adapter_css.contains("saturate(")).to_be(false)
expect(adapter_css.contains("color: transparent")).to_be(false)
expect(adapter_css.contains("background: transparent")).to_be(false)
expect(adapter_css.contains("background: #")).to_be(false)
expect(adapter_css.contains("border-color: #")).to_be(false)
expect(adapter_css.contains("box-shadow: 0")).to_be(false)
```

</details>

#### retains exact window, resize, hot-corner, and taskbar behavior

- retains exact window, resize, hot-corner, and taskbar behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains exact window, resize, hot-corner, and taskbar behavior")
val css = generate_css("aetheric_dark")
val marker = "/* Folder theme package theme=aetheric_dark"
val adapter_css = css.substring(0, css.index_of(marker))

expect(adapter_css).to_contain(".wm-window.minimized { display: none; }")
expect(adapter_css).to_contain(".wm-window.maximized { left: 0 !important; top: 0 !important; width: 100vw !important; height: calc(100vh - var(--ui-taskbar-reserved-height)) !important; border-radius: 0; }")
expect(adapter_css).to_contain(".wm-titlebar { display: grid; grid-template-columns: auto auto")
expect(adapter_css).to_contain(".wm-titlebar:active { cursor: grabbing; }")
expect(adapter_css).to_contain(".wm-titlebar-icon img, .wm-title-icon img, .wm-taskbar-icon img { width: 100%; height: 100%; object-fit: cover")
expect(adapter_css).to_contain("#wm-taskbar { position: fixed")
expect(adapter_css).to_contain(".wm-taskbar-section { display: flex; align-items: center")
expect(adapter_css).to_contain(".wm-taskbar-label { max-width: var(--ui-taskbar-label-max-width); overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }")
expect(adapter_css).to_contain(".wm-resize-n { left: 0; top: 0; right: 0")
expect(adapter_css).to_contain(".wm-resize-s { left: 0; bottom: 0; right: 0")
expect(adapter_css).to_contain(".wm-resize-e { right: 0; top: var(--ui-resize-edge-title-offset); bottom: 0")
expect(adapter_css).to_contain(".wm-resize-w { left: 0; top: var(--ui-resize-edge-title-offset); bottom: 0")
expect(adapter_css).to_contain(".wm-resize-ne { right: 0; top: 0")
expect(adapter_css).to_contain(".wm-resize-nw { left: 0; top: 0")
expect(adapter_css).to_contain(".wm-resize-se { right: 0; bottom: 0")
expect(adapter_css).to_contain(".wm-resize-sw { left: 0; bottom: 0")
expect(adapter_css).to_contain("cursor: n-resize")
expect(adapter_css).to_contain("cursor: sw-resize")
expect(adapter_css).to_contain(".wm-hot-corner-overview { left: max(var(--ui-hot-corner-offset), env(safe-area-inset-left)); top: max(var(--ui-hot-corner-offset), env(safe-area-inset-top)); }")
expect(adapter_css).to_contain(".wm-hot-corner-launcher { right: max(var(--ui-hot-corner-offset), env(safe-area-inset-right)); top: max(var(--ui-hot-corner-offset), env(safe-area-inset-top)); }")
expect(adapter_css).to_contain(".wm-hot-corner-desktop { left: max(var(--ui-hot-corner-offset), env(safe-area-inset-left)); bottom: max(var(--ui-hot-corner-offset), env(safe-area-inset-bottom)); }")
expect(adapter_css).to_contain(".wm-hot-corner-control-center { right: max(var(--ui-hot-corner-offset), env(safe-area-inset-right)); bottom: max(var(--ui-hot-corner-offset), env(safe-area-inset-bottom)); }")
expect(adapter_css).to_contain(".wm-window.dragging, .wm-window[data-resize-active='true']")
```

</details>

#### retains dialog, form-state, tooltip, tree, and responsive behavior

- retains dialog, form-state, tooltip, tree, and responsive behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains dialog, form-state, tooltip, tree, and responsive behavior")
val css = generate_css("aetheric_dark")
val marker = "/* Folder theme package theme=aetheric_dark"
val adapter_css = css.substring(0, css.index_of(marker))

expect(adapter_css).to_contain(".widget-dialog-overlay { position: fixed; inset: 0")
expect(adapter_css).to_contain(".widget-dialog { position: fixed; top: 50%; left: 50%")
expect(adapter_css).to_contain("transform: translate(-50%, -50%)")
expect(adapter_css).to_contain(".widget-button:disabled, .widget-button[disabled]")
expect(adapter_css).to_contain(".widget-input[readonly], .widget-textfield[readonly], .widget-textarea[readonly]")
expect(adapter_css).to_contain(".widget-input.error, .widget-textfield.error, .widget-textarea.error")
expect(adapter_css).to_contain(".tooltip-content { display: none; position: absolute; bottom: 100%; left: 50%")
expect(adapter_css).to_contain("margin-bottom: var(--ui-tooltip-margin-bottom); transform: translateX(-50%)")
expect(adapter_css).to_contain(".widget-tooltip:hover .tooltip-content, .widget-tooltip:focus-within .tooltip-content { display: block; }")
expect(adapter_css).to_contain(".tree-root { list-style: none; padding-left: 0; }")
expect(adapter_css).to_contain(".tree-node ul { list-style: none; padding-left: var(--ui-tree-indent); }")
expect(adapter_css).to_contain(".tree-toggle { cursor: pointer; display: inline-block")
expect(adapter_css).to_contain(".tree-label { cursor: pointer; padding: var(--ui-tree-label-padding)")
expect(adapter_css).to_contain(".tree-node.leaf .tree-label { padding-left: var(--ui-tree-leaf-label-indent); }")
expect(adapter_css).to_contain(".tree-node.collapsed > ul { display: none; } .tree-node.expanded > ul { display: block; }")
expect(adapter_css.contains(".tree-children")).to_be(false)
expect(adapter_css).to_contain("@media (max-width: 599px)")
expect(adapter_css).to_contain("@media (min-width: 600px) and (max-width: 839px)")
expect(adapter_css).to_contain(".widget-sidebar { display: none; }")
expect(adapter_css).to_contain("@media (prefers-reduced-motion: reduce)")
```

</details>

#### matches taskbar preview, context-menu, and generated tree DOM contracts

- matches taskbar preview, context-menu, and generated tree DOM contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches taskbar preview, context-menu, and generated tree DOM contracts")
val css = generate_css("aetheric_dark")
val marker = "/* Folder theme package theme=aetheric_dark"
val adapter_css = css.substring(0, css.index_of(marker))
val tree_dom_source = file_read("src/app/ui.render/html_widgets.spl")
val wm_dom_source = file_read("src/app/ui.web/wm.js")

expect(adapter_css).to_contain(".wm-taskbar-preview { width: var(--ui-taskbar-preview-width); min-height: var(--ui-taskbar-preview-min-height); display: grid; grid-template-columns: var(--ui-taskbar-preview-columns)")
expect(adapter_css).to_contain(".wm-taskbar-preview-icon { width: var(--ui-taskbar-preview-icon-size); height: var(--ui-taskbar-preview-icon-size); display: inline-grid; place-items: center; }")
expect(adapter_css).to_contain(".wm-taskbar-preview-body { min-width: 0; display: grid; gap: var(--ui-taskbar-preview-body-gap); }")
expect(adapter_css).to_contain(".wm-taskbar-preview-title, .wm-taskbar-preview-meta { min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }")
expect(adapter_css).to_contain(".wm-taskbar-preview-status { color: var(--ui-taskbar-preview-status-color)")
expect(adapter_css).to_contain(".wm-taskbar-preview-actions { grid-column: 1 / -1; display: flex; justify-content: flex-end")
expect(adapter_css).to_contain(".wm-taskbar-preview-action { width: var(--ui-taskbar-preview-action-size); height: var(--ui-taskbar-preview-action-size)")
expect(adapter_css).to_contain(".wm-window-context-header { min-width: 0; display: grid; grid-template-columns: var(--ui-window-context-header-columns)")
expect(adapter_css).to_contain(".wm-window-context-item { min-height: var(--ui-window-context-item-min-height); display: grid; grid-template-columns: var(--ui-window-context-item-columns)")
expect(adapter_css).to_contain(".wm-window-context-glyph { width: var(--ui-window-context-glyph-size); height: var(--ui-window-context-glyph-size)")

expect(tree_dom_source).to_contain("<ul class=\\\"tree-root\\\">")
expect(tree_dom_source).to_contain("<li class=\\\"tree-node{exp_class}\\\">")
expect(tree_dom_source).to_contain("<span class=\\\"tree-toggle\\\"")
expect(tree_dom_source).to_contain("<span class=\\\"tree-label\\\">")
expect(wm_dom_source).to_contain("preview.className = 'wm-taskbar-preview'")
expect(wm_dom_source).to_contain("actions.className = 'wm-taskbar-preview-actions'")
expect(wm_dom_source).to_contain("menu.className = 'wm-window-context-menu'")
```

</details>

#### keeps literal compatibility CSS outside the canonical package path

- keeps literal compatibility CSS outside the canonical package path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps literal compatibility CSS outside the canonical package path")
val source = file_read("src/app/ui.web/html_css.spl")
val package_css = file_read("config/themes/aetheric_dark/base.css")

expect(source).to_contain("if package_css != \"\":")
expect(source).to_contain("return generate_package_authoritative_css(")
expect(source).to_contain("val WM_TRAFFIC_CLOSE = \"#FF5F57\"")
expect(package_css).to_contain("--ui-traffic-close: #ff5f57")
expect(package_css).to_contain("--ui-surface-backdrop-filter:")
expect(package_css).to_contain("--ui-titlebar-focus-shadow:")
expect(package_css).to_contain("--ui-overlay-active-background:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui_web/html_css_theme_authority_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Web CSS package authority adapter.
- Web CSS package authority adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f02250c498ad643619e8cd8a9f25a3ff141990b9f90285417ae89a97501d2db8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f02250c498ad643619e8cd8a9f25a3ff141990b9f90285417ae89a97501d2db8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f02250c498ad643619e8cd8a9f25a3ff141990b9f90285417ae89a97501d2db8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ui_web/html_css_theme_authority_spec.spl
mirror: doc/06_spec/01_unit/app/ui_web/html_css_theme_authority_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui_web/html_css_theme_authority_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui_web/html_css_theme_authority_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui_web/html_css_theme_authority_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a newline-delimited structural adapter before the resolved package' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui_web/html_css_theme_authority_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps traffic-light pseudo-elements structural while the package owns paint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui_web/html_css_theme_authority_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains exact window, resize, hot-corner, and taskbar behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
